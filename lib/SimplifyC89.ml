(* Copyright (c) INRIA and Microsoft Corporation. All rights reserved. *)
(* Licensed under the Apache 2.0 and MIT Licenses. *)

(* A set of transformations for the sole purpose of bringing us closer to C89
 * compatibility, or to support function-level local variable hoisting
 * ([-fhoist-locals]). *)

open Ast
open Helpers

(* This phase precedes [hoist_bufcreate] and relies on [hoist].
 *
 * The pass is parameterized by [hoist_locals]:
 *
 * - [false] (default; serves [-fc89-scope]): the notion of scope is just the
 *   C scope (it's a cosmetic criterion). Each [if]/[else] branch and the
 *   body of a [for] loop is its own scope. Stack-allocated buffers under a
 *   let are left in place; [hoist_bufcreate] will take care of them later.
 *   Non-constant-size stack arrays (VLAs) are silently left in place;
 *   [fixup_c89] in [CStarToC11] will wrap them in an implicit block scope.
 *
 * - [true] (serves [-fhoist-locals]): the notion of scope is the function
 *   body, modulo [EPushFrame] which must remain a hoist barrier for the
 *   F* stack memory model to remain sound. Let-bindings in [if]/[else],
 *   [switch], [while], [for] bodies, and [match] arms all bubble up to the
 *   nearest enclosing [EPushFrame] (or function top). Constant-size
 *   stack-allocated buffers are funnelled through [mk_copy_assignment]
 *   (which emits [EBufWrite]s, never [EBufCreate]s left under an
 *   assignment). VLAs trigger warning 29 ([HoistLocalsVla]) and are left
 *   in place. *)
class hoist_lets_class (hoist_locals: bool) = object (self)

  inherit [_] map

  method private scope_start t e =
    (* We skip through actual let-bindings (which will generate declarations at
     * the beginning of a scope), then start hoisting. *)
    match e.node with
    | ELet (b, e1, e2) when not (List.mem MetaSequence b.node.meta) ->
        (* No ELet's in e1 so nothing to hoist *)
        with_type t (ELet (b, e1, self#scope_start t e2))
    | ELet (b, ({ node = EStandaloneComment _; _ } as e1), e2)
      when hoist_locals && List.mem MetaSequence b.node.meta ->
        (* Under [-fhoist-locals], a standalone comment in the declaration
         * zone is treated as part of the prefix: subsequent declarations
         * keep their initializers and the comment retains its position
         * relative to them. *)
        with_type t (ELet (b, e1, self#scope_start t e2))
    | _ ->
        let env = ref [] in
        let e = self#visit_expr_w env e in
        let bs = List.rev_map (fun b ->
          mark_mut b, any
        ) !env in
        nest bs t e

  method! visit_DFunction _ cc flags n_cg n ret name binders body =
    let body = self#scope_start ret body in
    DFunction (cc, flags, n_cg, n, ret, name, binders, body)

  method! visit_EIfThenElse (env, t) e1 e2 e3 =
    if hoist_locals then
      (* Bubble let-bindings from each branch up to the enclosing scope. *)
      EIfThenElse (
        self#visit_expr_w env e1,
        self#visit_expr_w env e2,
        self#visit_expr_w env e3)
    else
      (* No ELet's in e1 *)
      EIfThenElse (e1, self#scope_start t e2, self#scope_start t e3)

  method! visit_EFor (env, _) b e1 e2 e3 e4 =
    if hoist_locals then
      (* Keep the for-loop binder local to the loop iteration; the body's
       * let-bindings bubble up to the enclosing scope. *)
      EFor (b,
        self#visit_expr_w env e1,
        self#visit_expr_w env e2,
        self#visit_expr_w env e3,
        self#visit_expr_w env e4)
    else if List.mem MetaSequence b.node.meta then
      EFor (b, e1, e2, e3, self#scope_start TUnit e4)
    else
      let b, subst = DeBruijn.opening_binder b in
      let e2 = subst e2 in
      let e3 = subst e3 in
      let e4 = self#scope_start TUnit (subst e4) in
      env := b :: !env;
      EFor (sequence_binding (),
        with_unit (EAssign (with_type b.typ (EOpen (b.node.name, b.node.atom)), e1)),
        DeBruijn.lift 1 e2,
        DeBruijn.lift 1 e3,
        DeBruijn.lift 1 e4)

  method! visit_ELet (env, t) b e1 e2 =
    match e1.node with
    | EPushFrame ->
        (* EPushFrame is a hoist barrier under both modes: scope_start
         * restarts inside e2 so collected bindings land inside the
         * push_frame/pop_frame pair. *)
        ELet (b, e1, self#scope_start t e2)

    | _ when List.mem MetaSequence b.node.meta ->
        (* Under [-fhoist-locals], also visit e1: it may contain a
         * statement-position [EIfThenElse] or similar whose branches
         * carry let-bindings that should be hoisted. *)
        let e1 = if hoist_locals then self#visit_expr_w env e1 else e1 in
        let e2 = self#visit_expr_w env e2 in
        ELet (b, e1, e2)

    | EBufCreate (lifetime, _, _)
      when lifetime <> Common.Stack || not hoist_locals ->
        (* In C89 mode, leave all EBufCreate let-bindings in place
         * (hoist_bufcreate will deal with them later, possibly wrapping in
         * an implicit C block scope). In hoist-locals mode, only
         * non-Stack EBufCreates are left alone: they are heap/eternal
         * allocations whose [Assign(BufCreate _)] form would not be
         * uniformly handled by [CStarToC11], so they retain their
         * original let-binding. *)
        ELet (b, e1, self#scope_start t e2)

    | _ ->
        match strengthen_array' b.typ e1 with
        | Some typ when e1.node <> EAny ->
            let b, e2 = DeBruijn.open_binder b e2 in
            let b = { b with typ } in
            env := b :: !env;
            let e1 = if hoist_locals then self#visit_expr_w env e1 else e1 in
            let e2 = self#visit_expr_w env e2 in
            ELet (sequence_binding (),
              with_unit (
                match typ with
                | TArray (t, s) ->
                    mk_copy_assignment (t, s) (EOpen (b.node.name, b.node.atom)) e1
                | _ ->
                    EAssign (with_type b.typ (EOpen (b.node.name, b.node.atom)), e1)
              ),
              DeBruijn.lift 1 e2)
        | _ ->
            if hoist_locals then begin
              (* Non-constant-size stack array (VLA) that would have to
               * cross statements to reach the function top: not safe to
               * hoist (no fixed stack reservation possible). Warn and
               * leave in place. *)
              Warn.(maybe_fatal_error ("", HoistLocalsVla b.node.name));
              let e1 = self#visit_expr_w env e1 in
              let e2 = self#visit_expr_w env e2 in
              ELet (b, e1, e2)
            end else
              (* Can't hoist because someone uses a non-constant sized array on
               * the stack (argh!!!). AstToCStar will insert a new block scope
               * starting here to make sure it's valid C89... *)
              ELet (b, e1, self#scope_start t e2)
end

let hoist_lets = new hoist_lets_class false

let hoist_locals = new hoist_lets_class true
