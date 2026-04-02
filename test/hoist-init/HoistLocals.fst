module HoistLocals

(** Test for -fhoist-locals: variable hoisting to function top.
    Includes direct shadowing and various control flow patterns. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32

(* Simple function with sequential let-bindings *)
let simple (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = 1ul in
  let y = U32.(x +%^ 2ul) in
  let z = U32.(y +%^ 3ul) in
  z

(* Function with direct variable shadowing: x is bound twice *)
let shadow_direct (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = arg in
  let y = U32.(x +%^ 1ul) in
  let x = U32.(y +%^ 1ul) in
  U32.(x +%^ y)

(* Function with shadowing in if-then-else branches *)
let shadow_branch (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
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
let with_sequence (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = U32.(arg +%^ 1ul) in
  let y = U32.(x +%^ 2ul) in
  let z = U32.(x +%^ y) in
  z

(* Function with nested shadowing: same name used at multiple nesting levels *)
let nested_shadow (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = arg in
  let r =
    (let x = U32.(x +%^ 1ul) in
     let y = U32.(x +%^ 2ul) in
     let x = U32.(y +%^ 3ul) in
     x)
  in
  U32.(r +%^ x)

(* Multiple variables of different types *)
let multi_type (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let a = true in
  let b = 42ul in
  let c = 10ul in
  if a then
    U32.(b +%^ c)
  else
    U32.(b -%^ c)

(* Nested block via push_frame / pop_frame: variables inside the frame
   are hoisted to the function top, past the frame boundary. *)
let nested_frame (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = U32.(arg +%^ 1ul) in
  push_frame ();
  let y = U32.(x +%^ 2ul) in
  let z = U32.(y +%^ x) in
  pop_frame ();
  z

(* Variable shadowing inside a push_frame block:
   the inner x shadows the outer; after hoisting both are at function top. *)
let shadow_in_frame (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = arg in
  push_frame ();
  let x = U32.(x +%^ 10ul) in
  let y = U32.(x +%^ 1ul) in
  pop_frame ();
  U32.(y +%^ x)

(* Nested if-then-else with local variables at each nesting level.
   After hoisting, all branch-local variables move to function top. *)
let nested_ite (a: bool) (b: bool) (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  if a then begin
    let x = U32.(arg +%^ 1ul) in
    if b then begin
      let y = U32.(x +%^ 10ul) in
      y
    end else begin
      let y = U32.(x +%^ 20ul) in
      y
    end
  end else begin
    let x = U32.(arg +%^ 2ul) in
    if b then begin
      let y = U32.(x +%^ 30ul) in
      y
    end else begin
      let y = U32.(x +%^ 40ul) in
      y
    end
  end

(* Variables shared before nested if-then-else, with new bindings inside. *)
let shared_then_branch (a: bool) (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = U32.(arg +%^ 1ul) in
  let y = U32.(x +%^ x) in
  if a then begin
    let z = U32.(y +%^ 10ul) in
    U32.(z +%^ x)
  end else begin
    let z = U32.(y +%^ 20ul) in
    U32.(z +%^ x)
  end

(* Three levels of nested if-then-else with let-bindings at each level *)
let deep_nested_ite (a: bool) (b: bool) (c: bool) (arg: U32.t):
    Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  if a then begin
    let p = U32.(arg +%^ 1ul) in
    if b then begin
      let q = U32.(p +%^ 1ul) in
      if c then begin
        let r = U32.(q +%^ 1ul) in
        r
      end else begin
        let r = U32.(q +%^ 2ul) in
        r
      end
    end else begin
      let q = U32.(p +%^ 2ul) in
      q
    end
  end else begin
    let p = U32.(arg +%^ 2ul) in
    U32.(p +%^ p)
  end

(* Shadowing in nested if-then-else: same name bound in both branches *)
let shadow_nested_ite (a: bool) (arg: U32.t): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  let x = arg in
  if a then begin
    let x = U32.(x +%^ 10ul) in
    let y = U32.(x +%^ 1ul) in
    U32.(y +%^ x)
  end else begin
    let x = U32.(x +%^ 20ul) in
    let y = U32.(x +%^ 2ul) in
    U32.(y +%^ x)
  end

module B = LowStar.Buffer
open LowStar.BufferOps

(* Stack-allocated buffer with uniform initializer: should be hoisted as
   an uninitialized declaration + memset/fill at original site. *)
let buf_create_fill (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = B.alloca 42ul 4ul in
  let r = b.(0ul) in
  pop_frame ();
  r

(* Stack-allocated buffer with uniform initializer, followed by a write *)
let buf_create_write (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let b = B.alloca 0ul 4ul in
  b.(0ul) <- 99ul;
  let r = b.(0ul) in
  pop_frame ();
  r

(* Stack-allocated buffer with a scalar + buffer in the same function *)
let buf_and_scalar (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let x = 10ul in
  let b = B.alloca x 2ul in
  let r = U32.(b.(0ul) +%^ b.(1ul)) in
  pop_frame ();
  r

(* Buffer inside a branch: hoisted declaration, fill in branch *)
let buf_in_branch (flag: bool): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  if flag then begin
    let b = B.alloca 5ul 2ul in
    let r = U32.(b.(0ul) +%^ b.(1ul)) in
    pop_frame ();
    r
  end else begin
    let b = B.alloca 7ul 2ul in
    let r = U32.(b.(0ul) +%^ b.(1ul)) in
    pop_frame ();
    r
  end

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
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
  (* nested_frame: x=1, y=3, z=4 *)
  let nf = nested_frame 0ul in
  TestLib.checku32 nf 4ul;
  (* shadow_in_frame: outer x=0, inner x=10, y=11, ret=21 *)
  let sf = shadow_in_frame 0ul in
  TestLib.checku32 sf 21ul;
  (* nested_ite: various branch combinations *)
  let n1 = nested_ite true true 0ul in
  TestLib.checku32 n1 11ul;
  let n2 = nested_ite true false 0ul in
  TestLib.checku32 n2 21ul;
  let n3 = nested_ite false true 0ul in
  TestLib.checku32 n3 32ul;
  let n4 = nested_ite false false 0ul in
  TestLib.checku32 n4 42ul;
  (* shared_then_branch: x=1, y=2, z depends on branch *)
  let stb = shared_then_branch true 0ul in
  TestLib.checku32 stb 13ul;
  let stb0 = shared_then_branch false 0ul in
  TestLib.checku32 stb0 23ul;
  (* deep_nested_ite: 3 levels *)
  let d1 = deep_nested_ite true true true 0ul in
  TestLib.checku32 d1 3ul;
  let d2 = deep_nested_ite true true false 0ul in
  TestLib.checku32 d2 4ul;
  let d3 = deep_nested_ite true false true 0ul in
  TestLib.checku32 d3 3ul;
  let d4 = deep_nested_ite false false false 0ul in
  TestLib.checku32 d4 4ul;
  (* shadow_nested_ite: shadowing in branches *)
  let sn1 = shadow_nested_ite true 5ul in
  TestLib.checku32 sn1 31ul;
  let sn2 = shadow_nested_ite false 5ul in
  TestLib.checku32 sn2 52ul;
  (* buf_create_fill: buffer filled with 42, read [0] *)
  push_frame ();
  let bf = buf_create_fill () in
  TestLib.checku32 bf 42ul;
  (* buf_create_write: buffer filled with 0, then [0]:=99 *)
  let bw = buf_create_write () in
  TestLib.checku32 bw 99ul;
  (* buf_and_scalar: buffer filled with 10, read [0]+[1] *)
  let bs = buf_and_scalar () in
  TestLib.checku32 bs 20ul;
  (* buf_in_branch: buffer in branch *)
  let bb1 = buf_in_branch true in
  TestLib.checku32 bb1 10ul;
  let bb2 = buf_in_branch false in
  TestLib.checku32 bb2 14ul;
  pop_frame ();
  0l
