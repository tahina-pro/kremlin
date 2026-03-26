(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Coalesce hoisted declarations with their first assignments.
    After -fhoist-locals, function bodies have the shape:
      T1 x1; T2 x2; ...; x1 = v1; x2 = v2; ...; rest
    This pass turns them into:
      T1 x1 = v1; T2 x2 = v2; ...; rest
    when it is safe to do so (x is not referenced before its assignment). *)

module C = C11

module SSet = Set.Make(String)

(* Extract the variable name from a declarator. *)
let rec name_of_declarator (d: C.declarator): string =
  match d with
  | Ident n -> n
  | Pointer (_, d) | Array (_, d, _) | Function (_, d, _) -> name_of_declarator d

(* Collect all variable names referenced in a C11 expression. *)
let rec vars_of_expr (e: C.expr): SSet.t =
  match e with
  | Name n -> SSet.singleton n
  | Op1 (_, e) -> vars_of_expr e
  | Op2 (_, e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | Index (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | Deref e | Address e -> vars_of_expr e
  | Member (e1, e2) | MemberP (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | Assign (e1, e2) -> SSet.union (vars_of_expr e1) (vars_of_expr e2)
  | Call (e, es) ->
      List.fold_left (fun acc e -> SSet.union acc (vars_of_expr e)) (vars_of_expr e) es
  | Cast (_, e) -> vars_of_expr e
  | Sizeof e -> vars_of_expr e
  | MemberAccess (e, _) | MemberAccessPointer (e, _) -> vars_of_expr e
  | InlineComment (_, e, _) -> vars_of_expr e
  | Stmt stmts -> List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s)) SSet.empty stmts
  | CxxInitializerList init -> vars_of_init init
  | CompoundLiteral (_, inits) ->
      List.fold_left (fun acc i -> SSet.union acc (vars_of_init i)) SSet.empty inits
  | Literal _ | Constant _ | Bool _ | Type _ -> SSet.empty

and vars_of_init (i: C.init): SSet.t =
  match i with
  | InitExpr e -> vars_of_expr e
  | Designated (_, i) -> vars_of_init i
  | Initializer is ->
      List.fold_left (fun acc i -> SSet.union acc (vars_of_init i)) SSet.empty is

and vars_of_stmt (s: C.stmt): SSet.t =
  match s with
  | Compound stmts -> List.fold_left (fun acc s -> SSet.union acc (vars_of_stmt s)) SSet.empty stmts
  | Decl (_, _, _, _, _, dis) ->
      List.fold_left (fun acc (_, _, init) ->
        match init with Some i -> SSet.union acc (vars_of_init i) | None -> acc
      ) SSet.empty dis
  | Expr e -> vars_of_expr e
  | _ -> SSet.empty

(* Collect all variables mentioned in a list of declarations' initializers. *)
let vars_of_decl_inits (decls: C.stmt list): SSet.t =
  List.fold_left (fun acc (s: C.stmt) ->
    match s with
    | Decl (_, _, _, _, _, dis) ->
        List.fold_left (fun acc (_, _, init) ->
          match init with Some i -> SSet.union acc (vars_of_init i) | None -> acc
        ) acc dis
    | _ -> acc
  ) SSet.empty decls

(* Collect the LHS variable names from assignment statements in assigns. *)
let assigned_vars (assigns: C.stmt list): SSet.t =
  List.fold_left (fun acc (s: C.stmt) ->
    match s with
    | Expr (Assign (Name x, _)) -> SSet.add x acc
    | _ -> acc
  ) SSet.empty assigns

(* Collect all variables mentioned in values of assignments and initializers. *)
let vars_of_assigns (assigns: C.stmt list): SSet.t =
  List.fold_left (fun acc (s: C.stmt) ->
    match s with
    | Expr (Assign (_, v)) -> SSet.union acc (vars_of_expr v)
    | Decl (_, _, _, _, _, dis) ->
        List.fold_left (fun acc (_, _, init) ->
          match init with Some i -> SSet.union acc (vars_of_init i) | None -> acc
        ) acc dis
    | _ -> acc
  ) SSet.empty assigns

(* Check if a declaration for variable [name] exists and whether it's initialized. *)
type decl_status = NotFound | Uninitialized | Initialized

let find_decl (name: string) (decls: C.stmt list): decl_status =
  List.fold_left (fun acc (s: C.stmt) ->
    match acc, s with
    | NotFound, Decl (_, _, _, _, _, dis) ->
        if List.exists (fun (d, _, init) ->
          name_of_declarator d = name && init <> None
        ) dis then Initialized
        else if List.exists (fun (d, _, _) ->
          name_of_declarator d = name
        ) dis then Uninitialized
        else NotFound
    | _ -> acc
  ) NotFound decls

(* Remove the declaration for [name] from decls and return its declaration
   info so we can create an initialized version. Returns (updated_decls, removed_decl_or_none). *)
let remove_decl (name: string) (decls: C.stmt list):
    C.stmt list * (C.qualifier list * C.type_spec * C.inline_stance option * C.storage_spec option * C.extra * C.declarator * C.alignment option) option =
  let found = ref None in
  let decls = List.filter_map (fun (s: C.stmt) ->
    match s with
    | Decl (qs, spec, inline, stor, extra, dis) ->
        let matching, rest = List.partition (fun (d, _, _) ->
          name_of_declarator d = name
        ) dis in
        begin match matching with
        | [(d, align, _)] ->
            found := Some (qs, spec, inline, stor, extra, d, align);
            if rest = [] then None
            else Some (Decl (qs, spec, inline, stor, extra, rest) : C.stmt)
        | _ -> Some s
        end
    | _ -> Some s
  ) decls in
  decls, !found

(* The main recursive function: aux decls assigns body *)
let rec aux (decls: C.stmt list) (assigns: C.stmt list) (body: C.stmt list): C.stmt list =
  match body with
  | (Expr (Assign (Name x, v)) as assign_stmt : C.stmt) :: body' ->
      begin match find_decl x decls with
      | Initialized ->
          (* x is already initialized in decls: keep as assignment *)
          aux decls (assigns @ [assign_stmt]) body'
      | Uninitialized ->
          let mentioned = SSet.union (vars_of_assigns assigns) (vars_of_decl_inits decls) in
          let v_vars = vars_of_expr v in
          let lhs_vars = assigned_vars assigns in
          if SSet.mem x mentioned || not (SSet.is_empty (SSet.inter v_vars lhs_vars)) then
            (* x is mentioned in other initializers/assigns, or v references
               a variable that is assigned to in assigns: keep as assignment *)
            aux decls (assigns @ [assign_stmt]) body'
          else
            (* Safe to coalesce: remove uninitialized decl, append initialized decl *)
            let decls', removed = remove_decl x decls in
            begin match removed with
            | Some (qs, spec, inline, stor, extra, d, align) ->
                let init_decl = (Decl (qs, spec, inline, stor, extra,
                  [(d, align, Some (InitExpr v))]) : C.stmt) in
                aux (decls' @ [init_decl]) assigns body'
            | None ->
                decls @ assigns @ (assign_stmt :: body')
            end
      | NotFound ->
          (* x is not in our declarations: stop *)
          decls @ assigns @ (assign_stmt :: body')
      end
  | _ ->
      (* Not an assignment: stop *)
      decls @ assigns @ body

(* Split a statement list into leading declarations and the rest. *)
let split_decls (stmts: C.stmt list): C.stmt list * C.stmt list =
  let rec go decls = function
    | (Decl _ as d : C.stmt) :: rest -> go (decls @ [d]) rest
    | rest -> decls, rest
  in
  go [] stmts

let coalesce_body (s: C.stmt): C.stmt =
  match s with
  | Compound stmts ->
      let decls, body = split_decls stmts in
      Compound (aux decls [] body)
  | _ -> s

let coalesce_files (files: (string * C.program) list): (string * C.program) list =
  List.map (fun (name, program) ->
    let program = List.map (fun (df: C.declaration_or_function) ->
      match df with
      | Function (comments, decl, body) ->
          (Function (comments, decl, coalesce_body body) : C.declaration_or_function)
      | other -> other
    ) program in
    (name, program)
  ) files
