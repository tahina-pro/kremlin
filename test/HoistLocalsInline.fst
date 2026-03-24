module HoistLocalsInline

(** Test for -fhoist-locals with inline_for_extraction noextract functions.
    When these functions are inlined, their local variables may shadow
    variables in the caller. The hoisting pass should handle this correctly. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

(* An inline_for_extraction noextract helper that uses a local variable x *)
noextract
inline_for_extraction
let add_one (x: U32.t): St U32.t =
  let x = U32.(x +%^ 1ul) in
  x

(* Another inline helper that shadows with a different local name *)
noextract
inline_for_extraction
let double (w: U32.t): St U32.t =
  let x = U32.(w +%^ w) in
  x

(* Inline helper that creates multiple locals *)
noextract
inline_for_extraction
let compute (a: U32.t) (b: U32.t): St U32.t =
  let x = U32.(a +%^ b) in
  let y = U32.(x +%^ 1ul) in
  y

(* Test: caller uses variable x, then calls add_one which also uses x internally.
   After inlining, there will be shadowing of x. *)
let test_inline_shadow (): St U32.t =
  let x = 5ul in
  let y = add_one x in
  U32.(x +%^ y)

(* Test: multiple inlined calls, each introducing their own x *)
let test_multiple_inline (): St U32.t =
  let x = 1ul in
  let a = add_one x in
  let b = double a in
  let c = add_one b in
  U32.(c +%^ x)

(* Test: nested inline calls with shadowing at each level *)
let test_nested_inline (): St U32.t =
  let x = 3ul in
  let y = compute x (add_one x) in
  U32.(y +%^ x)

(* Test: inline calls inside branches *)
let test_branch_inline (cond: bool): St U32.t =
  let x = 10ul in
  if cond then begin
    let y = add_one x in
    let x = double y in
    x
  end else begin
    let y = double x in
    add_one y
  end

let main (): St Int32.t =
  let r1 = test_inline_shadow () in
  TestLib.checku32 r1 11ul;
  let r2 = test_multiple_inline () in
  TestLib.checku32 r2 6ul;
  let r3 = test_nested_inline () in
  TestLib.checku32 r3 11ul;
  let r4t = test_branch_inline true in
  TestLib.checku32 r4t 22ul;
  let r4f = test_branch_inline false in
  TestLib.checku32 r4f 21ul;
  0l
