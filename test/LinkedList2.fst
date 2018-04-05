module LinkedList2

module B = FStar.Buffer
module CN = C.Nullity
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32

open FStar.HyperStack.ST

#set-options "--__no_positivity --use_two_phase_tc true"

/// We revisit the classic example of lists, but in a low-level setting, using
/// linked lists. This first version uses `ref`, the type of references that are
/// always live. However, we don't cheat, and don't recall liveness "for free".
noeq
type t (a: Type0) =
//  CN.pointer_or_null (cell a)
  B.buffer (cell a)

and cell (a: Type0) = {
  next: t a;
  data: a;
}

/// Since linked lists go through a reference for indirection purposes, we
/// enrich lists with a predicate that captures their length. This predicate
/// will be needed for any traversal of the list, in order to show termination.
/// Some points of interest:
/// - the absence of cycles does not suffice to guarantee termination, as the
///   number of references in the heap is potentially infinite;
/// - the heap model allows us to select without showing liveness, which allows
///   to de-couple the length predicate from the liveness predicate. (YES, it allows us to, but it deserves nothing. )
let rec well_formed #a (h: HS.mem) (c: t a) (l: nat):
  GTot Type0 (decreases l)
= B.live h c /\ (
  if CN.is_null c
  then l = 0
  else
    B.length c == 1 /\ (
    let { next=next } = B.get h c 0 in
    if l = 0
    then
      false
    else
      well_formed h next (l - 1)
  ))

/// Note: all the ghost predicates and functions operate on a length of type
/// nat; the Ghost effect guarantees that the length can only be used at
/// run-time. Functions called at run-time will, conversely, use a length of
/// type `erased nat`, which states that the length is
/// computationally-irrelevant and can be safely removed from the resulting C
/// code via a combination of F* + KreMLin erasure.

/// When traversing a list `l` such that `well_formed h l n`, it is often
/// the case that we recursively visit the Cons cell, passing `n - 1` for the
/// recursive call. This lemma ensures that Z3 can show that `n - 1` has type
/// `nat`.
let cons_nonzero_length #a (h: HS.mem) (c: t a) (l: nat):
  Lemma
    (requires (well_formed h c l /\ not (CN.is_null c)))
    (ensures (l <> 0))
    [ SMTPat (well_formed h c l); SMTPat (CN.is_null c) ] =
    ()

let rec length_functional #a (h: HS.mem) (c: t a) (l1 l2: nat):
  Lemma
    (requires (well_formed h c l1 /\ well_formed h c l2))
    (ensures (l1 = l2))
    (decreases l1)
    [ SMTPat (well_formed h c l1); SMTPat (well_formed h c l2) ] =
  if CN.is_null c
  then ()
  else
    let { next=next } = B.get h c 0 in
    // Without `cons_nonzero_length`, we would need assert (l1 <> 0)
    length_functional h next (l1 - 1) (l2 - 1)

/// This form will rarely turn out to be useful, except perhaps for user code.
/// Indeed, we most often want to tie the length of the list in the final state
/// with its length in the original state.
let live #a (h: HS.mem) (l: t a) =
  exists n. well_formed #a h l n

let live_nil #a (h: HS.mem) (l: t a) : Lemma
  (requires (B.live h l /\ CN.is_null l))
  (ensures (live h l))
= assert (well_formed h l 0)

let live_cons #a (h: HS.mem) (l: t a) : Lemma
  (requires (B.live h l /\ B.length l == 1 /\ live h (B.get h l 0).next))
  (ensures (live h l))
= assert (forall n . well_formed h (B.get h l 0).next n ==> well_formed h l (n + 1))

/// Disjointness of a buffer wrt. a list of buffers of the same type

let rec disjoint_from_list (#a #b: Type) (r: B.buffer a) (l: list (B.buffer b)) : GTot Type0 =
  match l with
  | [] -> true
  | r' :: q -> B.disjoint r r' /\ disjoint_from_list r q

/// As we start proving some degree of functional correctness, we will have to
/// reason about non-interference, and state that some operations do not modify
/// the footprint of a given list.
#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: nat) -> Ghost (list (B.buffer (cell a)))
  (requires (well_formed h l n))
  (ensures (fun refs ->
    let n_refs = L.length refs in
    n_refs == n + 1 /\
    (forall (i: nat). {:pattern (L.index refs i)}
      i <= n ==> well_formed h (L.index refs i) (n - i))))
  (decreases n)

let rec footprint #a h l n =
  if CN.is_null l
  then [l]
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint h next (n - 1) in
    l :: refs
#reset-options

let rec modifies_disjoint_footprint
  (#a: Type)
  (#b: Type)
  (h: HS.mem)
  (l: t a)
  (n: nat)
  (r: B.buffer b)
  (h' : HS.mem)
: Lemma
  (requires (
    well_formed h l n /\
    disjoint_from_list r (footprint h l n) /\
    B.modifies_1 r h h'
  ))
  (ensures (
    well_formed h' l n /\
    footprint h' l n == footprint h l n
  ))
  (decreases n)
= if CN.is_null l
  then ()
  else
    let {next = l'} = B.get h l 0 in
    modifies_disjoint_footprint h l' (n - 1) r h'

let lemma_distinct_addrs_distinct_types2
  (#a:Type0) (#b:Type0) (#rel1: Preorder.preorder a) (#rel2: Preorder.preorder b) (h: Heap.heap) (r1:Heap.mref a rel1) (r2:Heap.mref b rel2)
  :Lemma (requires (a =!= b /\ h `Heap.contains` r1 /\ h `Heap.contains` r2))
         (ensures (Heap.addr_of r1 <> Heap.addr_of r2))
= ()

val lemma_distinct_addrs_distinct_types3
  (#a:Type0) (#b:Type0) (#rel1: Preorder.preorder a) (#rel2: Preorder.preorder b) (h: HS.mem) (r1: HS.mreference a rel1) (r2:HS.mreference b rel2)
  :Lemma ((a =!= b /\ h `HS.contains` r1 /\ h `HS.contains` r2) ==> (HS.frameOf r1 <> HS.frameOf r2 \/ HS.as_addr r1 <> HS.as_addr r2))

let lemma_distinct_addrs_distinct_types3 #a #b #rel1 #rel2 h r1 r2 =
  if HS.frameOf r1 = HS.frameOf r2
  then
    Classical.move_requires (lemma_distinct_addrs_distinct_types2 #a #b #rel1 #rel2 (Map.sel h.HS.h (HS.frameOf r1)) (HS.as_ref r1)) (HS.as_ref r2)
  else ()

let buffer_distinct_sel_disjoint
  (#a1 #a2: Type)
  (b1: B.buffer a1)
  (b2: B.buffer a2)
  (h: HS.mem)
: Lemma
  (requires (
    B.length b1 == 1 /\
    B.length b2 == 1 /\
    B.live h b1 /\
    B.live h b2 /\
    (a1 == a2 ==> B.get h b1 0 =!= B.get h b2 0)
  ))
  (ensures (
    B.disjoint b1 b2
  ))
= if B.frameOf b1 = B.frameOf b2
  then begin
    lemma_distinct_addrs_distinct_types3 h (B.content b1) (B.content b2);
    Heap.lemma_distinct_addrs_distinct_mm ();
    assume (B.disjoint b1 b2)
  end
  else ()

let rec well_formed_distinct_lengths_disjoint
  #a1 #a2
  (c1: B.buffer (cell a1))
  (c2: B.buffer (cell a2))
  (n1: nat)
  (n2: nat)
  (h: HS.mem)
: Lemma
  (requires (
    well_formed h c1 n1 /\
    well_formed h c2 n2 /\
    n1 <> n2
  ))
  (ensures (
    B.disjoint c1 c2
  ))
  (decreases (n1 + n2))
= assume (not (CN.is_null c1 || CN.is_null c2));
  begin
    let {next = next1} = B.get h c1 0 in
    let {next = next2} = B.get h c2 0 in
    well_formed_distinct_lengths_disjoint next1 next2 (n1 - 1) (n2 - 1) h;
    buffer_distinct_sel_disjoint c1 c2 h
  end // else assume (B.disjoint c1 c2)

let rec well_formed_gt_lengths_disjoint_from_list
  #a1 #a2
  (h: HS.mem)
  (c1: ref (cell a1))
  (c2: ref (cell a2))
  (n1: nat)
  (n2: nat)
: Lemma
  (requires (well_formed h c1 n1 /\ well_formed h c2 n2 /\ n1 > n2))
  (ensures (disjoint_from_list c1 (footprint h c2 n2)))
  (decreases n2)
= well_formed_distinct_lengths_disjoint c1 c2 n1 n2 h;
  if n2 = 0
  then ()
  else well_formed_gt_lengths_disjoint_from_list h c1 (Cons?.next (HS.sel h c2)) n1 (n2 - 1)

let well_formed_head_tail_disjoint
  #a
  (h: HS.mem)
  (c: ref (cell a))
  (n: nat)
: Lemma
  (requires (well_formed h c n))
  (ensures (let (hd :: tl) = footprint h c n in hd == c /\ disjoint_from_list c tl))
= if n = 0
  then ()
  else well_formed_gt_lengths_disjoint_from_list h c (Cons?.next (HS.sel h c)) n (n - 1)

let rec unused_in_well_formed_disjoint_from_list
  #a #b
  (h: HS.mem)
  (r: ref a)
  (l: ref (cell b))
  (n: nat)
: Lemma
  (requires (r `HS.unused_in` h /\ well_formed h l n))
  (ensures (disjoint_from_list r (footprint h l n)))
  (decreases n)
= if n = 0
  then ()
  else unused_in_well_formed_disjoint_from_list h r (Cons?.next (HS.sel h l)) (n - 1)

/// Finally, the pop operation. Our representation of linked lists is slightly
/// unusual, owing to the fact that we do not have null references, and
/// therefore represent the empty list as a reference to `Nil`. This means that
/// popping an element off the front of the list can be done by merely writing
/// the next cell in that reference. This is in contrast to the classic
/// representation using null pointers, which requires the client to pass a
/// pointer to a pointer, which is then filled with the address of the next
/// cell, or null if this was the last element in the list.

/// The code is straightforward and crucially relies on the call to the lemma
/// above. Note that at this stage we do not prove full functional correctness
/// of our implementation. Rather, we just state that the lengths is as
/// expected.

/// This version uses an erased integer n; we have to work a little bit to
/// hide/reveal the computationally-irrelevant length.
val pop: (#a: Type) -> (#n: G.erased nat) -> (l: t a) ->
  Stack (option a)
  (requires (fun h -> well_formed h l (G.reveal n)))
  (ensures (fun h0 v h1 ->
    let n = G.reveal n in
    match v with
    | None -> n = 0 /\ well_formed h1 l n
    | Some _ -> n > 0 /\ well_formed h1 l (n - 1)
  ))

let pop #a #n l =
  match !l with
  | Nil -> None
  | Cons next data ->
      let h0 = get () in
      l := !next;
      let h1 = get () in
      well_formed_head_tail_disjoint h0 l (G.reveal n);
      modifies_disjoint_footprint h0 next (G.reveal n - 1) l h1;
      Some data

val push: (#a: Type) -> (#n: G.erased nat) -> (l: t a) -> (x: a) ->
  ST unit
    (requires (fun h -> well_formed h l (G.reveal n)))
    (ensures (fun h0 () h1 -> well_formed h1 l (G.reveal n + 1)))

let push #a #n l x =
  let h0 = get () in
  let c: ref (cell a) = ralloc HS.root !l in
  unused_in_well_formed_disjoint_from_list h0 c l (G.reveal n);
  let h1 = get () in
  modifies_disjoint_footprint h0 l (G.reveal n) c h1;
  l := Cons c x;
  let h2 = get () in
  well_formed_head_tail_disjoint h0 l (G.reveal n);
  modifies_disjoint_footprint h1 c (G.reveal n) l h2


/// Connecting our predicate `well_formed` to the regular length function.
/// Note that this function takes a list whose length is unknown statically,
/// because of the existential quantification.
/// TODO: figure out why the `assert` is needed.
val length (#a: Type) (gn: G.erased nat) (l: t a): Stack UInt32.t
  (requires (fun h -> well_formed h l (G.reveal gn)))
  (ensures (fun h0 n h1 ->
    h0 == h1 /\
    U32.v n = G.reveal gn
  ))

/// Note that we could have as easily returned an option, but sometimes fatal
/// errors are just easier to handle for client code. The `C.String` module
/// provides facilities for dealing with constant C string literals. It reveals
/// that they are zero-terminated and allows looping over them if one wants to,
/// say, copy an immutable constant string into a mutable buffer.
let rec length #a gn l =
  match !l with
  | Nil ->
      let h = get () in
      assert (well_formed h l 0);
      0ul
  | Cons next _ ->
      let open U32 in
      let h = get () in
      let n = length (G.hide (G.reveal gn - 1)) next in
      if n = 0xfffffffful then begin
        C.String.(print !$"Integer overflow while computing length");
        C.exit 255l;
        0ul
      end else
        n +^ 1ul
  
val main: unit -> ST (Int32.t) (fun _ -> true) (fun _ _ _ -> true)
let main () =
  let l: ref (cell Int32.t) = ralloc HS.root Nil in
  push #Int32.t #(G.hide 0) l 1l;
  push #Int32.t #(G.hide 1) l 0l;
  match pop #Int32.t #(G.hide 2) l with
  | None -> 1l
  | Some x -> x
