module MergeDeclInit

(** Tests for the declaration-initialization merge pass (MergeDeclInit).
    With -fhoist-locals, local declarations are hoisted to function top
    as uninitialized declarations followed by assignments. The merge pass
    folds them back when safe. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32
module LC = LowStar.Comment

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
  0l
