(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(** Hoisting all local variable declarations to the beginning of a function. *)

open Ast
open DeBruijn
open PrintAst

let debug = Options.debug "hoist-locals"

(* Determines if an ELet binding involves stack storage that cannot be hoisted
   at all: non-empty EBufCreateL with per-element initializers, or
   EBufCreate with a non-constant size. *)
let has_storage (_t: typ) (e1: expr) =
  match e1.node with
  | EBufCreateL (Stack, _ :: _) ->
      true
  | EBufCreate (Stack, _, { node = EConstant _; _ }) ->
      false
  | EBufCreate (Stack, _, _) ->
      true
  | _ ->
      false

(* Build the hoisted initializer expression for a binder.  For buffer
   creations we keep an uninitialized buffer of the right size so that
   later passes (hoist_bufcreate) see a proper EBufCreate node. *)
let hoisted_init (b: binder) (e1: expr): expr =
  match e1.node with
  | EBufCreate (Stack, _, size) ->
      { node = EBufCreate (Stack, { node = EAny; typ = Helpers.assert_tbuf_or_tarray b.typ; meta = [] }, size);
        typ = b.typ; meta = [] }
  | EBufCreateL (Stack, []) ->
      e1
  | _ ->
      { node = EAny; typ = b.typ; meta = [] }

(* Walk the expression tree, collecting ELet binders that should be hoisted
   and replacing them with assignments. Returns the list of collected
   (binder, init) pairs (outermost first) and the transformed expression. *)
let rec collect (e: expr): (binder * expr) list * expr =
  let w n = { node = n; typ = e.typ; meta = e.meta } in
  match e.node with
  | ELet (b, e1, e2) when not (List.mem MetaSequence b.node.meta) ->
      let b, e2 = open_binder b e2 in
      (* Collect from the initializer *)
      let bs1, e1 = collect e1 in
      (* Collect from the continuation *)
      let bs2, e2 = collect e2 in
      if has_storage b.typ e1 then begin
        (* Stack buffer that cannot be hoisted: emit appropriate warning *)
        (match e1.node with
         | EBufCreateL (Stack, _ :: _) ->
             Warn.maybe_fatal_error ("", Error.BufCreateLNotHoisted
               ([""], b.node.name))
         | EBufCreate (Stack, _, _) ->
             Warn.maybe_fatal_error ("", Error.BufCreateNonConstant
               ([""], b.node.name))
         | _ -> ());
        let e2 = close_binder b e2 in
        bs1 @ bs2, w (ELet (b, e1, e2))
      end
      else
        (* Hoist this binder *)
        let assignment =
          match e1.node with
          | EAny ->
              (* Already uninitialized: no assignment needed *)
              e2
          | EBufCreate (Stack, { node = EAny; _ }, _)
          | EBufCreateL (Stack, []) ->
              (* Uninitialized buffer: no fill needed *)
              e2
          | EBufCreate (Stack, init, size) ->
              (* Buffer with uniform initializer: replace with EBufFill *)
              w (ELet (Helpers.sequence_binding (),
                { node = EBufFill (
                    { node = EOpen (b.node.name, b.node.atom); typ = b.typ; meta = [] },
                    init, size);
                  typ = TUnit; meta = [] },
                e2))
          | _ ->
              (* Replace with: let _ = b := e1 in e2 *)
              w (ELet (Helpers.sequence_binding (),
                { node = EAssign (
                    { node = EOpen (b.node.name, b.node.atom); typ = b.typ; meta = [] },
                    e1);
                  typ = TUnit; meta = [] },
                e2))
        in
        (* Mark the binder as mutable since it will be assigned to *)
        let b = { b with node = { b.node with mut = true } } in
        bs1 @ [(b, hoisted_init b e1)] @ bs2, assignment

  | ELet (b, e1, e2) ->
      (* Sequence binding: collect from sub-expressions but don't hoist the binding *)
      let bs1, e1 = collect e1 in
      let b', e2 = open_binder b e2 in
      let bs2, e2 = collect e2 in
      let e2 = close_binder b' e2 in
      bs1 @ bs2, w (ELet (b, e1, e2))

  | EIfThenElse (e1, e2, e3) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      let bs3, e3 = collect e3 in
      bs1 @ bs2 @ bs3, w (EIfThenElse (e1, e2, e3))

  | EWhile (e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EWhile (e1, e2))

  | EFor (b, e1, e2, e3, e4) ->
      let bs1, e1 = collect e1 in
      let b', e2 = open_binder b e2 in
      let b'', e3 = open_binder b e3 in
      let b''', e4 = open_binder b e4 in
      let bs2, e2 = collect e2 in
      let bs3, e3 = collect e3 in
      let bs4, e4 = collect e4 in
      let e2 = close_binder b' e2 in
      let e3 = close_binder b'' e3 in
      let e4 = close_binder b''' e4 in
      bs1 @ bs2 @ bs3 @ bs4, w (EFor (b, e1, e2, e3, e4))

  | ESwitch (e1, cases) ->
      let bs1, e1 = collect e1 in
      let bss, cases = List.split (List.map (fun (c, e) ->
        let bs, e = collect e in
        bs, (c, e)
      ) cases) in
      bs1 @ List.concat bss, w (ESwitch (e1, cases))

  | EReturn e1 ->
      let bs, e1 = collect e1 in
      bs, w (EReturn e1)

  | EAssign (e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EAssign (e1, e2))

  | ECast (e1, t) ->
      let bs, e1 = collect e1 in
      bs, w (ECast (e1, t))

  | EIgnore e1 ->
      let bs, e1 = collect e1 in
      bs, w (EIgnore e1)

  | EApp (e1, es) ->
      let bs1, e1 = collect e1 in
      let bss, es = List.split (List.map collect es) in
      bs1 @ List.concat bss, w (EApp (e1, es))

  | EBufRead (e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EBufRead (e1, e2))

  | EBufCreate (l, e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EBufCreate (l, e1, e2))

  | EBufCreateL (l, es) ->
      let bss, es = List.split (List.map collect es) in
      List.concat bss, w (EBufCreateL (l, es))

  | EBufWrite (e1, e2, e3) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      let bs3, e3 = collect e3 in
      bs1 @ bs2 @ bs3, w (EBufWrite (e1, e2, e3))

  | EBufSub (e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EBufSub (e1, e2))

  | EBufDiff (e1, e2) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      bs1 @ bs2, w (EBufDiff (e1, e2))

  | EBufBlit (e1, e2, e3, e4, e5) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      let bs3, e3 = collect e3 in
      let bs4, e4 = collect e4 in
      let bs5, e5 = collect e5 in
      bs1 @ bs2 @ bs3 @ bs4 @ bs5, w (EBufBlit (e1, e2, e3, e4, e5))

  | EBufFill (e1, e2, e3) ->
      let bs1, e1 = collect e1 in
      let bs2, e2 = collect e2 in
      let bs3, e3 = collect e3 in
      bs1 @ bs2 @ bs3, w (EBufFill (e1, e2, e3))

  | EBufFree e1 ->
      let bs, e1 = collect e1 in
      bs, w (EBufFree e1)

  | EField (e1, f) ->
      let bs, e1 = collect e1 in
      bs, w (EField (e1, f))

  | EAddrOf e1 ->
      let bs, e1 = collect e1 in
      bs, w (EAddrOf e1)

  | EFlat fieldexprs ->
      let fs, es = List.split fieldexprs in
      let bss, es = List.split (List.map collect es) in
      List.concat bss, w (EFlat (List.combine fs es))

  | EMatch (flavor, e1, branches) ->
      let bs1, e1 = collect e1 in
      let bss, branches = List.split (List.map (fun (binders, pat, body) ->
        let binders, pat, body = open_branch binders pat body in
        let bs, body = collect body in
        let pat, body = close_branch binders pat body in
        bs, (binders, pat, body)
      ) branches) in
      bs1 @ List.concat bss, w (EMatch (flavor, e1, branches))

  | ETuple es ->
      let bss, es = List.split (List.map collect es) in
      List.concat bss, w (ETuple es)

  | ESequence es ->
      let bss, es = List.split (List.map collect es) in
      List.concat bss, w (ESequence es)

  | EFun (_, _, _) ->
      (* Don't hoist out of nested functions *)
      [], e

  (* Leaf nodes: no sub-expressions to recurse into *)
  | EBound _ | EOpen _ | EQualified _ | EConstant _ | EUnit | EBool _
  | EString _ | EAny | EOp _ | EPolyComp _ | EPushFrame | EPopFrame
  | EEnum _ | EStandaloneComment _ | EAbort _ | EBufNull
  | EBreak | EContinue | ECons _ ->
      [], e

  | ETApp (e1, cgs, cgs', ts) ->
      let bs, e1 = collect e1 in
      bs, w (ETApp (e1, cgs, cgs', ts))

(* Wrap a body with hoisted declarations. The binders list is outermost-first,
   meaning the first binder in the list becomes the outermost ELet. *)
let wrap_with_hoisted (binders: (binder * expr) list) (body: expr): expr =
  List.fold_right (fun (b, init) body ->
    let body = close_binder b body in
    { node = ELet (b, init, body);
      typ = body.typ;
      meta = [] }
  ) binders body

let hoist_visitor = object(_)
  inherit [_] map
  method! visit_DFunction () cc flags n_cgs n ret name binders body =
    if debug then
      KPrint.bprintf "Hoist locals: visiting %a\n%a\n" plid name ppexpr body;
    let binders, body = open_binders binders body in
    let hoisted, body = collect body in
    let body = wrap_with_hoisted hoisted body in
    let body = close_binders binders body in
    DFunction (cc, flags, n_cgs, n, ret, name, binders, body)
end

let simplify files =
  let files = Simplify.sequence_to_let#visit_files () files in
  let files = hoist_visitor#visit_files () files in
  let files = Simplify.let_to_sequence#visit_files () files in
  files
