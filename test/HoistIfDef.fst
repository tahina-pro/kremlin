module HoistIfDef

(** Test for -fhoist-locals with CIfDef: hoisted variables used in only
    one branch of a #if should get KRML_MAYBE_UNUSED_VAR. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

[@ CIfDef ]
assume val use_feature: bool

let helper (x: U32.t): St U32.t = U32.(x +%^ 1ul)

(* Variable 'a' is only used in the true branch;
   variable 'b' is only used in the false branch.
   Both should be hoisted and marked maybe_unused. *)
let test_ifdef_branch (): St U32.t =
  if use_feature then begin
    let a = helper 10ul in
    U32.(a +%^ a)
  end else begin
    let b = helper 20ul in
    U32.(b +%^ 1ul)
  end

(* Variable 'c' is used in both branches, so it should NOT be marked unused. *)
let test_ifdef_common (arg: U32.t): St U32.t =
  let c = helper arg in
  if use_feature then
    U32.(c +%^ 10ul)
  else
    U32.(c +%^ 20ul)

let main (): St Int32.t =
  let _ = test_ifdef_branch () in
  let _ = test_ifdef_common 0ul in
  0l
