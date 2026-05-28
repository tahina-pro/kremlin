module HoistMalloc

open FStar.HyperStack.ST
open FStar.UInt32
open LowStar.Printf
open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack

(* Test hoisting of Heap-allocated buffers ([B.malloc]) and
   Eternal-allocated buffers ([B.gcmalloc]) under [-fhoist-locals].

   Under [-fhoist-locals], the pointer declaration is hoisted to the
   function top as [T *buf = NULL;] while the actual
   [KRML_HOST_CALLOC] / [KRML_HOST_MALLOC] call stays at the original
   site as a separate [buf = ...;] assignment.  Allocations that
   already sit at the function-top declaration zone (no preceding
   statement) remain in their combined
   [T *buf = KRML_HOST_CALLOC(...)] form. *)

(* Heap malloc after a printf: under [-fhoist-locals], the declaration
   is hoisted ahead of the printf and the calloc call stays after it. *)
let test_malloc_after_stmt (): St unit =
  let x = 5ul in
  printf "test_malloc_after_stmt: MARKER x=%ul\n" x done;
  let buf = B.malloc HS.root 0ul 4ul in
  buf.(0ul) <- x;
  buf.(1ul) <- x +^ 1ul;
  buf.(2ul) <- x +^ 2ul;
  buf.(3ul) <- x +^ 3ul;
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  let v2 = buf.(2ul) in
  let v3 = buf.(3ul) in
  printf "test_malloc_after_stmt: %ul %ul %ul %ul\n" v0 v1 v2 v3 done;
  B.free buf

(* Heap malloc at function top with no preceding statement: stays
   combined in both modes. *)
let test_malloc_in_prefix (): St unit =
  let buf = B.malloc HS.root 7ul 2ul in
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  printf "test_malloc_in_prefix: %ul %ul\n" v0 v1 done;
  B.free buf

(* Two Heap mallocs after a single printf: both declarations are
   hoisted, both allocation calls stay at their original sites. *)
let test_multiple_malloc (): St unit =
  printf "test_multiple_malloc: MARKER two mallocs to follow\n" done;
  let a = B.malloc HS.root 1ul 2ul in
  let b = B.malloc HS.root 2ul 3ul in
  let va = a.(0ul) in
  let vb = b.(0ul) in
  printf "test_multiple_malloc: %ul %ul\n" va vb done;
  B.free a;
  B.free b

(* Eternal gcmalloc after a printf: same split as for [B.malloc],
   since both [Heap] and [Eternal] go through [mk_eternal_bufcreate]. *)
let test_gcmalloc_after_stmt (): St unit =
  printf "test_gcmalloc_after_stmt: MARKER gcmalloc to follow\n" done;
  let buf = B.gcmalloc HS.root 9ul 3ul in
  let v0 = buf.(0ul) in
  let v1 = buf.(1ul) in
  let v2 = buf.(2ul) in
  printf "test_gcmalloc_after_stmt: %ul %ul %ul\n" v0 v1 v2 done

val main: FStar.Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  St C.exit_code
let main argc argv =
  push_frame ();
  test_malloc_after_stmt ();
  test_malloc_in_prefix ();
  test_multiple_malloc ();
  test_gcmalloc_after_stmt ();
  pop_frame ();
  C.EXIT_SUCCESS
