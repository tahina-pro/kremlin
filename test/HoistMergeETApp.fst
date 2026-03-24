module HoistMergeETApp

(** Test for -fhoist-locals -fmerge: exercises ETApp nodes
    (polymorphic function applications) that survive monomorphization. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

(* Use LowStar.Ignore.ignore which produces ETApp nodes *)
let test_ignore (): St U32.t =
  let x = 1ul in
  LowStar.Ignore.ignore x;
  let y = U32.(x +%^ 2ul) in
  LowStar.Ignore.ignore y;
  let x = U32.(y +%^ 3ul) in
  x

(* Use LowStar.Ignore.ignore inside branches with shadowing *)
let test_branch (arg: U32.t): St U32.t =
  let x = arg in
  LowStar.Ignore.ignore x;
  if U32.(x >^ 0ul) then begin
    let x = U32.(x +%^ 10ul) in
    LowStar.Ignore.ignore x;
    x
  end else begin
    let x = U32.(x +%^ 20ul) in
    LowStar.Ignore.ignore x;
    x
  end

let main (): St Int32.t =
  let r1 = test_ignore () in
  TestLib.checku32 r1 6ul;
  let r2 = test_branch 5ul in
  TestLib.checku32 r2 15ul;
  let r3 = test_branch 0ul in
  TestLib.checku32 r3 20ul;
  0l
