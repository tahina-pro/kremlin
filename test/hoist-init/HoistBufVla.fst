module HoistBufVla

(** Test for -fhoist-locals with a non-constant-size stack buffer.
    Warning 31 (BufCreateNonConstant) is silenced for this test. *)

open FStar.HyperStack.ST

module U32 = FStar.UInt32
module B = LowStar.Buffer
open LowStar.BufferOps

(* Helper that returns a non-constant size *)
let get_size (): Stack (x:U32.t{U32.v x > 0 /\ U32.v x <= 256})
    (fun _ -> true) (fun _ _ _ -> true) =
  4ul

(* Buffer with non-constant size: cannot be hoisted, stays in place *)
let buf_non_const_size (): Stack U32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let n = get_size () in
  let b = B.alloca 42ul n in
  let r = b.(0ul) in
  pop_frame ();
  r

let main (): Stack Int32.t (fun _ -> true) (fun _ _ _ -> true) =
  push_frame ();
  let r = buf_non_const_size () in
  TestLib.checku32 r 42ul;
  pop_frame ();
  0l
