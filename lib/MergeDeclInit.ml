(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** After -fhoist-locals, merge back uninitialized declarations with their
    first assignments when safe: [T y; ...; y = w;] becomes [...; T y = w;].
    Runs before -finit-locals. Iterates until no more merges are possible. *)

module C = C11

module SSet = Set.Make(String)

let rec name_of_declarator (d: C.declarator): string option =
  match d with
  | Ident n -> Some n
  | Pointer (_, d) | Array (_, d, _) | Function (_, d, _) -> name_of_declarator d

(* Variable-name collectors for C11 expressions, initializers and statements. *)
let rec vars_of_expr (e: C.expr): SSet.t =
  match e with
  | C.Name n -> SSet.singleton n
  | C.Op1 (_, e) | C.Deref e | C.Address e | C.Sizeof e
  | C.MemberAccess (e, _) | C.MemberAccessPointer (e, _)
  | C.InlineComment (_, e, _) | C.Cast (_, e) -> vars_of_expr e
  | C.Op2 (_, e1, e2) | C.Index (e1, e2) | C.Member (e1, e2)
  | C.MemberP (e1, e2) | C.Assign (e1, e2) ->
      SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | C.Call (e, es) ->
      List.fold_left (fun acc e -> SSet.union acc (vars_of_expr e))
        (vars_of_expr e) es
  | C.CompoundLiteral (_, inits) -> vars_of_inits inits
  | C.Stmt stmts ->
      List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s))
        SSet.empty stmts
  | C.CxxInitializerList init -> vars_of_init init
  | C.Literal _ | C.Constant _ | C.Bool _ | C.Type _ -> SSet.empty

and vars_of_init (i: C.init): SSet.t =
  match i with
  | C.InitExpr e -> vars_of_expr e
  | C.Designated (_, i) -> vars_of_init i
  | C.Initializer is -> vars_of_inits is

and vars_of_inits (is: C.init list): SSet.t =
  List.fold_left (fun acc i -> SSet.union acc (vars_of_init i)) SSet.empty is

and vars_of_stmt (s: C.stmt): SSet.t =
  match s with
  | Compound stmts ->
      List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s))
        SSet.empty stmts
  | Decl (_, _, _, _, _, di) ->
      List.fold_left (fun acc ((_, _, init): C.declarator_and_init) ->
        match init with Some i -> SSet.union acc (vars_of_init i) | None -> acc
      ) SSet.empty di
  | Expr e -> vars_of_expr e
  | If (e, s) -> SSet.union (vars_of_expr e) (vars_of_stmt s)
  | IfElse (e, s1, s2) ->
      SSet.union (vars_of_expr e)
        (SSet.union (vars_of_stmt s1) (vars_of_stmt s2))
  | IfDef (e, ss1, elifs, ss2) ->
      let fold_stmts =
        List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s)) in
      let acc = vars_of_expr e in
      let acc = fold_stmts acc ss1 in
      let acc = List.fold_left
        (fun acc (e, ss) -> fold_stmts (SSet.union acc (vars_of_expr e)) ss)
        acc elifs in
      fold_stmts acc ss2
  | While (e, s) -> SSet.union (vars_of_expr e) (vars_of_stmt s)
  | For (de, e1, e2, s) ->
      let acc = match de with
        | `Decl (_, _, _, _, _, di) ->
            List.fold_left (fun acc ((_, _, init): C.declarator_and_init) ->
              match init with Some i -> SSet.union acc (vars_of_init i)
              | None -> acc
            ) SSet.empty di
        | `Expr e -> vars_of_expr e
        | `Skip -> SSet.empty
      in
      SSet.union acc (SSet.union (vars_of_expr e1)
        (SSet.union (vars_of_expr e2) (vars_of_stmt s)))
  | Return (Some e) -> vars_of_expr e
  | Return None | Break | Continue | Comment _ -> SSet.empty
  | Switch (e, cases, default) ->
      let acc = vars_of_expr e in
      let acc = List.fold_left
        (fun acc (_, s) -> SSet.union acc (vars_of_stmt s)) acc cases in
      SSet.union acc (vars_of_stmt default)

let vars_of_declaration ((_, _, _, _, _, di): C.declaration): SSet.t =
  List.fold_left (fun acc ((_, _, init): C.declarator_and_init) ->
    match init with Some i -> SSet.union acc (vars_of_init i) | None -> acc
  ) SSet.empty di

(** Try to perform one merge step on the top-level statement list of a
    function body.  Scans the prefix of [Decl] statements; if the first
    non-[Decl] is an assignment [y = w] whose target [y] is declared
    without initializer and [y] does not appear in any declaration
    initializer, merge them.  Returns [Some stmts'] on success. *)
let try_merge_one (stmts: C.stmt list): C.stmt list option =
  let rec split_prefix rev_decls (ss: C.stmt list) = match ss with
    | (Decl d : C.stmt) :: rest -> split_prefix (d :: rev_decls) rest
    | rest -> (List.rev rev_decls, rest)
  in
  let decls, rest = split_prefix [] stmts in
  match (rest : C.stmt list) with
  | Expr (C.Assign (C.Name y, w)) :: after ->
      let init_vars = List.fold_left
        (fun acc d -> SSet.union acc (vars_of_declaration d))
        SSet.empty decls
      in
      if SSet.mem y init_vars then None
      else
        let rec find rev_acc = function
          | [] -> None
          | ((qs, spec, inl, stor, extra, [(decl, align, None)])
              : C.declaration) :: rest
            when name_of_declarator decl = Some y ->
              let merged : C.declaration =
                (qs, spec, inl, stor, extra,
                 [(decl, align, Some (C.InitExpr w))])
              in
              Some (List.map (fun d -> (Decl d : C.stmt))
                      (List.rev_append rev_acc rest)
                    @ [(Decl merged : C.stmt)] @ after)
          | d :: rest -> find (d :: rev_acc) rest
        in
        find [] decls
  | _ -> None

let rec merge_until_fixpoint stmts =
  match try_merge_one stmts with
  | Some stmts' -> merge_until_fixpoint stmts'
  | None -> stmts

let merge_body (s: C.stmt): C.stmt =
  match s with
  | Compound stmts -> Compound (merge_until_fixpoint stmts)
  | _ -> s

let merge_decl_init_files
    (files: (string * C.program) list): (string * C.program) list =
  List.map (fun (name, program) ->
    let program = List.map (fun (df: C.declaration_or_function) ->
      match df with
      | Function (comments, decl, body) ->
          (Function (comments, decl, merge_body body)
            : C.declaration_or_function)
      | other -> other
    ) program in
    (name, program)
  ) files
