module MergeDeclInit

(** Tests for the declaration-initialization merge pass (MergeDeclInit).
    With -fhoist-locals, local declarations are hoisted to function top
    as uninitialized declarations followed by assignments. The merge pass
    folds them back when safe. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32
module LC = LowStar.Comment
module LI = LowStar.Ignore

(* All sequential bindings should merge back after hoisting.
   Using each variable more than once to prevent inlining. *)
let test_all_merge (): St U32.t =
  let a = 1ul in
  let b = U32.(a +%^ a) in
  let c = U32.(b +%^ a) in
  U32.(c +%^ b)

(* Chain of four dependent bindings: all should merge iteratively *)
let test_chain (): St U32.t =
  let w = 1ul in
  let x = U32.(w +%^ w) in
  let y = U32.(x +%^ w) in
  let z = U32.(y +%^ x) in
  U32.(z +%^ w)

(* Only the bindings before the branch should merge;
   bindings inside branches cannot merge. *)
let test_partial (flag: bool): St U32.t =
  let x = 1ul in
  let y = U32.(x +%^ x) in
  if flag then begin
    let r = U32.(y +%^ 10ul) in
    U32.(r +%^ x)
  end else begin
    let r = U32.(y +%^ 20ul) in
    U32.(r +%^ x)
  end

(* A standalone comment between bindings should not prevent merging *)
let test_comment_between (): St U32.t =
  let a = 1ul in
  LC.comment "standalone comment between a and b";
  let b = U32.(a +%^ a) in
  U32.(b +%^ a)

(* Comments before the first assignment: should still merge *)
let test_comment_before_assign (flag: bool): St U32.t =
  let x = 1ul in
  let y = U32.(x +%^ x) in
  LC.comment "comment before branch";
  if flag then begin
    let r = U32.(y +%^ 10ul) in
    U32.(r +%^ x)
  end else begin
    let r = U32.(y +%^ 20ul) in
    U32.(r +%^ x)
  end

(* Multiple comments interspersed with bindings *)
let test_multi_comment (): St U32.t =
  LC.comment "comment at start";
  let a = 1ul in
  LC.comment "comment after a";
  let b = U32.(a +%^ a) in
  LC.comment "comment after b";
  let c = U32.(b +%^ a) in
  U32.(c +%^ b)

(* An unused parameter generates KRML_MAYBE_UNUSED_VAR;
   the merge pass should skip it and still merge the bindings. *)
let test_unused_param (unused: U32.t) (arg: U32.t): St U32.t =
  LI.ignore unused;
  let a = U32.(arg +%^ 1ul) in
  let b = U32.(a +%^ a) in
  U32.(b +%^ a)

(* Two unused parameters before bindings *)
let test_two_unused (u1: U32.t) (u2: U32.t) (arg: U32.t): St U32.t =
  LI.ignore u1;
  LI.ignore u2;
  let a = U32.(arg +%^ 1ul) in
  let b = U32.(a +%^ a) in
  U32.(b +%^ a)

(* Mix of unused parameter, comment and bindings *)
let test_unused_and_comment (unused: U32.t) (arg: U32.t): St U32.t =
  LI.ignore unused;
  LC.comment "comment after ignore";
  let a = U32.(arg +%^ 1ul) in
  let b = U32.(a +%^ a) in
  U32.(b +%^ a)

let main (): St Int32.t =
  let r1 = test_all_merge () in
  TestLib.checku32 r1 5ul;
  let r2 = test_chain () in
  TestLib.checku32 r2 6ul;
  let r3 = test_partial true in
  TestLib.checku32 r3 13ul;
  let r4 = test_partial false in
  TestLib.checku32 r4 23ul;
  let r5 = test_comment_between () in
  TestLib.checku32 r5 3ul;
  let r6 = test_comment_before_assign true in
  TestLib.checku32 r6 13ul;
  let r7 = test_comment_before_assign false in
  TestLib.checku32 r7 23ul;
  let r8 = test_multi_comment () in
  TestLib.checku32 r8 5ul;
  (* test_unused_param: a=2, b=4, ret=6 *)
  let r9 = test_unused_param 99ul 1ul in
  TestLib.checku32 r9 6ul;
  (* test_two_unused: a=2, b=4, ret=6 *)
  let r10 = test_two_unused 99ul 88ul 1ul in
  TestLib.checku32 r10 6ul;
  (* test_unused_and_comment: a=2, b=4, ret=6 *)
  let r11 = test_unused_and_comment 99ul 1ul in
  TestLib.checku32 r11 6ul;
  0l
