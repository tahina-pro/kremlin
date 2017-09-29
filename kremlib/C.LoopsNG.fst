(* This module exposes a series of combinators; they are modeled using
 * higher-order functions and specifications, and extracted, using a
 * meta-theoretic argument, to actual C loops. *)
module C.LoopsNG

open FStar.HyperStack.ST
open FStar.BufferNG

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module UInt32 = FStar.UInt32
module P = FStar.Pointer

include Spec.Loops

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(** The functions in this module use the following convention:
 *  - the first arguments are buffers;
 *  - the destination buffer comes first, followed by the input buffer (as in
 *    C's memcpy)
 *  - each buffer is followed by its length; if several buffers share the same
 *    length, there is a single length argument after the buffers
 *  - the function-specific arguments come next (e.g. the number of times one
 *    may want to call the function in [repeat])
 *  - the second to last argument is the loop invariant (which may have
 *    dependencies on all the parameters before)
 *  - the last argument is the loop body (that will depend on the invariant, and
 *    possibly all the other parameters before. *)


(* Generic-purpose for-loop combinators ***************************************)

(* These combinators enjoy first-class support in KreMLin. (See [combinators] in
 * src/Simplify.ml *)

(* Currently extracting as:
    for (int i = <start>; i != <finish>; ++i)
      <f> i;
*)
val for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i + 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec for start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    for (UInt32.(start +^ 1ul)) finish inv f
  end

(* To be extracted as:
    for (int i = <start>; i != <finish>; --i)
      <f> i;
*)
val reverse_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish <= UInt32.v start} ->
  inv:(HS.mem -> nat -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start >= v i /\ v i > v finish)} -> Stack unit
                        (requires (fun h -> inv h (UInt32.v i)))
                        (ensures (fun h_1 _ h_2 -> UInt32.(inv h_1 (v i) /\ inv h_2 (v i - 1)))) ) ->
  Stack unit
    (requires (fun h -> inv h (UInt32.v start)))
    (ensures (fun _ _ h_2 -> inv h_2 (UInt32.v finish)))
let rec reverse_for start finish inv f =
  if start = finish then
    ()
  else begin
    f start;
    reverse_for (UInt32.(start -^ 1ul)) finish inv f
  end

(* To be extracted as:
    int i = <start>;
    bool b = false;
    for (; (!b) && (i != <end>); ++i) {
      b = <f> i;
    }
    // i and b must be in scope after the loop
*)
val interruptible_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish >= UInt32.v start} ->
  inv:(HS.mem -> nat -> bool -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start <= v i /\ v i < v finish)} -> Stack bool
                        (requires (fun h -> inv h (UInt32.v i) false))
                        (ensures (fun h_1 b h_2 -> inv h_1 (UInt32.v i) false /\ inv h_2 UInt32.(v i + 1) b)) ) ->
  Stack (UInt32.t * bool)
    (requires (fun h -> inv h (UInt32.v start) false))
    (ensures (fun _ res h_2 -> let (i, b) = res in ((if b then True else i == finish) /\ inv h_2 (UInt32.v i) b)))
let rec interruptible_for start finish inv f =
  if start = finish then
    (finish, false)
  else
    let start' = UInt32.(start +^ 1ul) in
    if f start
    then (start', true)
    else interruptible_for start' finish inv f

(* To be extracted as:
    while (true) {
      bool b = <f> i;
      if (b) {
         break;
      }
    }
*)
val do_while:
  inv:(HS.mem -> bool -> GTot Type0) ->
  f:(unit -> Stack bool
            (requires (fun h -> inv h false))
            (ensures (fun h_1 b h_2 -> inv h_1 false /\ inv h_2 b)) ) ->
  Stack unit
    (requires (fun h -> inv h false))
    (ensures (fun _ _ h_2 -> inv h_2 true))
let rec do_while inv f =
  let break = f () in
  if break
     then ()
     else do_while inv f

(* To be extracted as:
    int i = <start>;
    bool b = false;
    for (; (!b) && (i != <end>); --i) {
      b = <f> i;
    }
    // i and b must be in scope after the loop
*)
val interruptible_reverse_for:
  start:UInt32.t ->
  finish:UInt32.t{UInt32.v finish <= UInt32.v start} ->
  inv:(HS.mem -> nat -> bool -> GTot Type0) ->
  f:(i:UInt32.t{UInt32.(v start >= v i /\ v i > v finish)} -> Stack bool
                        (requires (fun h -> inv h (UInt32.v i) false))
                        (ensures (fun h_1 b h_2 -> inv h_1 (UInt32.v i) false /\ inv h_2 UInt32.(v i - 1) b)) ) ->
  Stack (UInt32.t * bool)
    (requires (fun h -> inv h (UInt32.v start) false))
    (ensures (fun _ res h_2 -> let (i, b) = res in ((if b then True else i == finish) /\ inv h_2 (UInt32.v i) b)))
let rec interruptible_reverse_for start finish inv f =
  if start = finish then
    (finish, false)
  else
    let start' = UInt32.(start -^ 1ul) in
    if f start
    then (start', true)
    else interruptible_reverse_for start' finish inv f


let get (#a: typ) (h: HS.mem) (b: buffer a) (i: nat) : Ghost (P.type_of_typ a) (requires (i < length b)) (ensures (fun _ -> True)) =
  Seq.index (as_seq h b) i

(* Non-primitive combinators that can be expressed in terms of the above ******)

#reset-options "--z3rlimit 100"

(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   out[i] = <f>(in[i]);
 *)
inline_for_extraction
val map:
  #a:typ -> #b:typ ->
  output: buffer b ->
  input: buffer a{disjoint input output} ->
  l: UInt32.t{ UInt32.v l = BufferNG.length output /\ UInt32.v l = BufferNG.length input } ->
  f:((P.type_of_typ a) -> Tot (P.type_of_typ b)) ->
  Stack unit
    (requires (fun h -> live h input /\ live h output ))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer output) h_1 h_2 /\ live h_2 input /\ live h_1 input /\ live h_2 output
      /\ live h_2 output
      /\ (let s1 = as_seq h_1 input in
         let s2 = as_seq h_2 output in
         s2 == seq_map f s1) ))

private
let seq_map_eq(#a: typ) (#b: typ) (sa:Seq.seq (P.type_of_typ a)) (sb:(Seq.seq (P.type_of_typ b))) (f:((P.type_of_typ a) -> Tot (P.type_of_typ b))) (i: nat) : GTot Type0 =
Seq.length sa == Seq.length sb /\ i <= Seq.length sa /\ (forall (j: nat) . j < i ==> Seq.index sb j == f (Seq.index sa j))

private
let lemma_seq_map_eq_elim_typ (#a: typ) (#b: typ) (sa:Seq.seq (P.type_of_typ a)) (sb:(Seq.seq (P.type_of_typ b))) (f:((P.type_of_typ a) -> Tot (P.type_of_typ b))) : Lemma
  (requires (seq_map_eq sa sb f (Seq.length sa)))
  (ensures (sb == seq_map f sa))
= Seq.lemma_eq_intro sb (seq_map f sa)

private
let lemma_seq_map_eq_intro_0
 (#a: typ) (#b: typ) (sa:Seq.seq (P.type_of_typ a)) (sb:(Seq.seq (P.type_of_typ b))) (f:((P.type_of_typ a) -> Tot (P.type_of_typ b))) : Lemma
 (requires (Seq.length sa == Seq.length sb))
 (ensures (seq_map_eq sa sb f 0))
= ()

inline_for_extraction
let map #a #b output input l f =
  let h0 = HST.get() in
  let inv (h1: HS.mem) (i: nat): GTot Type0 =
    live h1 output /\ live h1 input /\ P.modifies (P.loc_buffer output) h0 h1 /\ i <= UInt32.v l
    /\ seq_map_eq (as_seq h0 input) (as_seq h1 output) f i
  in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
  //    (requires (fun h -> inv h (UInt32.v i)))
  //    (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // = admit()
  // //   // let xi = input.(i) in
  // //   // output.(i) <- f xi
  // in
  // lemma_seq_map_eq_intro_0 (as_seq h0 input) (as_seq h0 output) f;
//  assert (inv h0 0);
//  for 0ul l inv f';
  let h1 = HST.get() in
  assume (inv h1 (UInt32.v l));
  assert (let sa = as_seq h0 input in let sb = as_seq h1 output in seq_map_eq sa sb f (Seq.length sa));
  // lemma_seq_map_eq_elim_typ (as_seq h0 input) (as_seq h1 output) f;
  (* admit *)
//  Seq.lemma_eq_intro (as_seq h1 output) (seq_map f (as_seq h0 input));
  admit()


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   out[i] = <f>(in1[i], in2[i]);
 *)
inline_for_extraction
val map2:
  #a:typ -> #b:typ -> #c:typ ->
  output: buffer c ->
  in1: buffer a{disjoint output in1} -> in2: buffer b{disjoint output in2} ->
  l: UInt32.t{ UInt32.v l = BufferNG.length output /\ UInt32.v l = BufferNG.length in1
     /\ UInt32.v l = BufferNG.length in2 } ->
  f:((P.type_of_typ a) -> (P.type_of_typ b) -> Tot (P.type_of_typ c)) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2 /\ live h output ))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer output) h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2 /\ live h_2 output
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 output in
         s == seq_map2 f s1 s2) ))

inline_for_extraction
let map2 #a #b #c output in1 in2 l f = admit()
  // let h0 = HST.get() in
  // let inv (h1: HS.mem) (i: nat): Type0 =
  //   live h1 output /\ live h1 in1 /\ live h1 in2 /\ P.modifies (P.loc_buffer output) h0 h1 /\ i <= UInt32.v l
  //   /\ (forall (j:nat). {:pattern (get h1 output j)} (j >= i /\ j < UInt32.v l) ==> get h1 output j == get h0 output j)
  //   /\ (forall (j:nat). {:pattern (get h1 output j)} j < i ==> get h1 output j == f (get h0 in1 j) (get h0 in2 j))
  // in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
  //   (requires (fun h -> inv h (UInt32.v i)))
  //   (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // =
  //   let xi = in1.(i) in
  //   let yi = in2.(i) in
  //   output.(i) <- f xi yi
  // in
  // for 0ul l inv f';
  // let h1 = HST.get() in
  // Seq.lemma_eq_intro (as_seq h1 output) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


(** Extracts as:
 * for (int i = 0; i < <l>; ++i)
 *   b[i] = <f>(b[i]);
 *)
inline_for_extraction
val in_place_map:
  #a:typ ->
  b: buffer a ->
  l: UInt32.t{ UInt32.v l = BufferNG.length b } ->
  f:((P.type_of_typ a) -> Tot (P.type_of_typ a)) ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer b) h_1 h_2 /\ live h_2 b /\ live h_1 b
      /\ (let s1 = as_seq h_1 b in
         let s2 = as_seq h_2 b in
         s2 == seq_map f s1) ))

inline_for_extraction
let in_place_map #a b l f = admit()
  // let h0 = HST.get() in
  // let inv (h1: HS.mem) (i: nat): Type0 =
  //   live h1 b /\ P.modifies (P.loc_buffer b) h0 h1 /\ i <= UInt32.v l
  //   /\ (forall (j:nat). {:pattern (get h1 b j)} (j >= i /\ j < UInt32.v l) ==> get h1 b j == get h0 b j)
  //   /\ (forall (j:nat). {:pattern (get h1 b j)} j < i ==> get h1 b j == f (get h0 b j))
  // in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
  //   (requires (fun h -> inv h (UInt32.v i)))
  //   (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // =
  //   let xi = b.(i) in
  //   b.(i) <- f xi
  // in
  // for 0ul l inv f';
  // let h1 = HST.get() in
  // Seq.lemma_eq_intro (as_seq h1 b) (seq_map f (as_seq h0 b))


(** Extracts as (destination buffer comes first):
 * for (int i = 0; i < <l>; ++i)
 *   in1[i] = <f>(in1[i], in2[i]);
 *)
inline_for_extraction
val in_place_map2:
  #a:typ -> #b:typ ->
  in1: buffer a ->
  in2: buffer b{disjoint in1 in2} ->
  l: UInt32.t{ UInt32.v l = BufferNG.length in1 /\ UInt32.v l = BufferNG.length in2} ->
  f:((P.type_of_typ a) -> (P.type_of_typ b) -> Tot (P.type_of_typ a)) ->
  Stack unit
    (requires (fun h -> live h in1 /\ live h in2))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer in1) h_1 h_2 /\ live h_2 in1 /\ live h_2 in2
      /\ live h_1 in1 /\ live h_1 in2
      /\ (let s1 = as_seq h_1 in1 in
         let s2 = as_seq h_1 in2 in
         let s = as_seq h_2 in1 in
         s == seq_map2 f s1 s2) ))
inline_for_extraction
let in_place_map2 #a #b in1 in2 l f = admit()
  // let h0 = HST.get() in
  // let inv (h1: HS.mem) (i: nat): Type0 =
  //   live h1 in1 /\ live h1 in2 /\ modifies_1 in1 h0 h1 /\ i <= UInt32.v l
  //   /\ (forall (j:nat). {:pattern (get h1 in1 j)} (j >= i /\ j < UInt32.v l) ==> get h1 in1 j == get h0 in1 j)
  //   /\ (forall (j:nat). {:pattern (get h1 in1 j)} j < i ==> get h1 in1 j == f (get h0 in1 j) (get h0 in2 j))
  // in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v l ) }): Stack unit
  //   (requires (fun h -> inv h (UInt32.v i)))
  //   (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // =
  //   let xi = in1.(i) in
  //   let yi = in2.(i) in
  //   in1.(i) <- f xi yi
  // in
  // for 0ul l inv f';
  // let h1 = HST.get() in
  // Seq.lemma_eq_intro (as_seq h1 in1) (seq_map2 f (as_seq h0 in1) (as_seq h0 in2))


#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"


(* Repeating the same operation a number of times over a buffer ***************)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

(** To be extracted as:
 * for (int i = 0; i < n; ++i)
 *   f(b[i]);
 *)
inline_for_extraction
val repeat:
  #a:typ ->
  l: UInt32.t ->
  f:(s:Seq.seq (P.type_of_typ a){Seq.length s = UInt32.v l} -> Tot (s':Seq.seq (P.type_of_typ a){Seq.length s' = Seq.length s})) ->
  b: buffer a{BufferNG.length b = UInt32.v l} ->
  max:UInt32.t ->
  fc:(b:buffer a{length b = UInt32.v l} -> Stack unit
                     (requires (fun h -> live h b))
                     (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ P.modifies (P.loc_buffer b) h0 h1
                       /\ (let b0 = as_seq h0 b in
                          let b1 = as_seq h1 b in
                          b1 == f b0)))) ->
  Stack unit
    (requires (fun h -> live h b ))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer b) h_1 h_2 /\ live h_1 b /\ live h_2 b
      /\ (let s = as_seq h_1 b in
         let s' = as_seq h_2 b in
         s' == repeat_spec (UInt32.v max) f s) ))
inline_for_extraction
let repeat #a l f b max fc = admit()
  // let h0 = HST.get() in
  // let inv (h1: HS.mem) (i: nat): Type0 =
  //   live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v max
  //   /\ as_seq h1 b == repeat_spec i f (as_seq h0 b)
  // in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): Stack unit
  //   (requires (fun h -> inv h (UInt32.v i)))
  //   (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // =
  //   fc b;
  //   lemma_repeat (UInt32.v i + 1) f (as_seq h0 b)
  // in
  // lemma_repeat_0 0 f (as_seq h0 b);
  // for 0ul max inv f'


(** To be extracted as:
 * for (int i = min; i < max; ++i)
 *   f(b[i], i);
 *)
inline_for_extraction
val repeat_range:
  #a:typ ->
  l: UInt32.t ->
  min:UInt32.t ->
  max:UInt32.t{UInt32.v min <= UInt32.v max} ->
  f:(s:Seq.seq (P.type_of_typ a){Seq.length s = UInt32.v l} -> i:nat{i < UInt32.v max} -> Tot (s':Seq.seq (P.type_of_typ a){Seq.length s' = Seq.length s})) ->
  b: buffer a{BufferNG.length b = UInt32.v l} ->
  fc:(b:buffer a{length b = UInt32.v l} -> i:UInt32.t{UInt32.v i < UInt32.v max} -> Stack unit
                     (requires (fun h -> live h b))
                     (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ P.modifies (P.loc_buffer b) h0 h1
                       /\ (let b0 = as_seq h0 b in
                          let b1 = as_seq h1 b in
                          b1 == f b0 (UInt32.v i))))) ->
  Stack unit
    (requires (fun h -> live h b ))
    (ensures (fun h_1 r h_2 -> P.modifies (P.loc_buffer b) h_1 h_2 /\ live h_1 b /\ live h_2 b
      /\ (let s = as_seq h_1 b in
         let s' = as_seq h_2 b in
         s' == repeat_range_spec (UInt32.v min) (UInt32.v max) f s) ))
inline_for_extraction
let repeat_range #a l min max f b fc = admit()
  // let h0 = HST.get() in
  // let inv (h1: HS.mem) (i: nat): Type0 =
  //   live h1 b /\ modifies_1 b h0 h1 /\ i <= UInt32.v max /\ UInt32.v min <= i
  //   /\ as_seq h1 b == repeat_range_spec (UInt32.v min) i f (as_seq h0 b)
  // in
  // let f' (i:UInt32.t{ UInt32.( 0 <= v i /\ v i < v max ) }): Stack unit
  //   (requires (fun h -> inv h (UInt32.v i)))
  //   (ensures (fun h_1 _ h_2 -> UInt32.(inv h_2 (v i + 1))))
  // =
  //   fc b i;
  //   lemma_repeat_range_spec (UInt32.v min) (UInt32.v i + 1) f (as_seq h0 b)
  // in
  // lemma_repeat_range_0 (UInt32.v min) (UInt32.v min) f (as_seq h0 b);
  // for min max inv f'
