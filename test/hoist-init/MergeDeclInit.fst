module MergeDeclInit

(** Tests for the declaration-initialization merge pass (MergeDeclInit).
    With -fhoist-locals, local declarations are hoisted to function top
    as uninitialized declarations followed by assignments. The merge pass
    folds them back when safe. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

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

let main (): St Int32.t =
  let r1 = test_all_merge () in
  TestLib.checku32 r1 5ul;
  let r2 = test_chain () in
  TestLib.checku32 r2 6ul;
  let r3 = test_partial true in
  TestLib.checku32 r3 13ul;
  let r4 = test_partial false in
  TestLib.checku32 r4 23ul;
  0l
