module HoistLocals

(** Test for -fhoist-locals: variable hoisting to function top.
    Includes direct shadowing and various control flow patterns. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

(* Simple function with sequential let-bindings *)
let simple (): St U32.t =
  let x = 1ul in
  let y = U32.(x +%^ 2ul) in
  let z = U32.(y +%^ 3ul) in
  z

(* Function with direct variable shadowing: x is bound twice *)
let shadow_direct (arg: U32.t): St U32.t =
  let x = arg in
  let y = U32.(x +%^ 1ul) in
  let x = U32.(y +%^ 1ul) in
  U32.(x +%^ y)

(* Function with shadowing in if-then-else branches *)
let shadow_branch (arg: U32.t): St U32.t =
  let x = arg in
  if U32.(x >^ 0ul) then begin
    let x = U32.(x +%^ 10ul) in
    let y = U32.(x +%^ 1ul) in
    y
  end else begin
    let x = U32.(x +%^ 20ul) in
    let y = U32.(x +%^ 2ul) in
    y
  end

(* Function with nested let-bindings in a sequence *)
let with_sequence (arg: U32.t): St U32.t =
  let x = U32.(arg +%^ 1ul) in
  let y = U32.(x +%^ 2ul) in
  let z = U32.(x +%^ y) in
  z

(* Function with nested shadowing: same name used at multiple nesting levels *)
let nested_shadow (arg: U32.t): St U32.t =
  let x = arg in
  let r =
    (let x = U32.(x +%^ 1ul) in
     let y = U32.(x +%^ 2ul) in
     let x = U32.(y +%^ 3ul) in
     x)
  in
  U32.(r +%^ x)

(* Multiple variables of different types *)
let multi_type (): St U32.t =
  let a = true in
  let b = 42ul in
  let c = 10ul in
  if a then
    U32.(b +%^ c)
  else
    U32.(b -%^ c)

let main (): St Int32.t =
  let s = simple () in
  TestLib.checku32 s 6ul;
  let sd = shadow_direct 0ul in
  TestLib.checku32 sd 3ul;
  let sb = shadow_branch 5ul in
  TestLib.checku32 sb 16ul;
  let sb0 = shadow_branch 0ul in
  TestLib.checku32 sb0 22ul;
  let ws = with_sequence 0ul in
  TestLib.checku32 ws 4ul;
  let ns = nested_shadow 0ul in
  TestLib.checku32 ns 6ul;
  let mt = multi_type () in
  TestLib.checku32 mt 52ul;
  0l
