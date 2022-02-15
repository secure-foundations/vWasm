module Common.AppendOptimizedList

#reset-options "--fuel 0 --ifuel 0"

open FStar.Calc

module L = FStar.List.Tot
module LP = FStar.List.Pure

unopteq
type chunk : Type0 -> Type u#1 =
  | List : #x:Type0 -> nat -> list x -> chunk x
  | Repeat : #x:Type0 -> nat -> x -> chunk x
  | Append : #x:Type0 -> nat -> chunk x -> chunk x -> chunk x
  | Zip : #x:Type0 -> #y:Type0 -> nat -> chunk x -> chunk y -> chunk (x & y)
  | UnzipFst : #x:Type0 -> #y:Type0 -> nat -> chunk (x & y) -> chunk x
  | UnzipSnd : #x:Type0 -> #y:Type0 -> nat -> chunk (x & y) -> chunk y

let rec weak_l_zip (l:list 'a) (r:list 'b) : list ('a & 'b) =
  allow_inversion (list 'a);
  allow_inversion (list 'b);
  match l, r with
  | [], [] -> []
  | [], _ | _, [] -> []
  | h1 :: t1, h2 :: t2 -> (h1, h2) :: weak_l_zip t1 t2

#push-options "--fuel 1"
let rec l_repeat #t (l:nat) (v:t) : (r:list t{L.length r == l}) =
  match l with
  | 0 -> []
  | _ -> v :: l_repeat (l - 1) v
#pop-options

(* Slow but convenient interpretation of chunks. Kept as GTot because slow. *)
let rec chunk_as_list (c:chunk 'a) : GTot (list 'a) =
  allow_inversion (chunk 'a);
  match c with
  | List _ l -> l
  | Repeat n x -> l_repeat n x
  | Append _ l r -> L.append (chunk_as_list l) (chunk_as_list r)
  | Zip _ l r -> weak_l_zip (chunk_as_list l) (chunk_as_list r)
  | UnzipFst _ l -> fst (L.unzip (chunk_as_list l))
  | UnzipSnd _ l -> snd (L.unzip (chunk_as_list l))

let actual_length_of_chunk (c:chunk 'a) : GTot nat = L.length (chunk_as_list c)

let fast_length_of_chunk (c:chunk 'a) : Tot nat =
  allow_inversion (chunk 'a);
  match c with
  | List n _
  | Repeat n _
  | Append n _ _
  | Zip n _ _
  | UnzipFst n _
  | UnzipSnd n _
    -> n

let rec valid_fast_length (c:chunk 'a) : GTot Type0 =
  allow_inversion (chunk 'a);
  (fast_length_of_chunk c == actual_length_of_chunk c) /\ (
    match c with
    | List n l -> True
    | Repeat n x -> True
    | Append n l r ->
      valid_fast_length l /\ valid_fast_length r /\
      (fast_length_of_chunk l + fast_length_of_chunk r == n)
    | Zip n l r ->
      valid_fast_length l /\ valid_fast_length r /\
      (fast_length_of_chunk l == n) /\
      (fast_length_of_chunk r == n)
    | UnzipFst n l ->
      valid_fast_length l /\
      (fast_length_of_chunk l == n)
    | UnzipSnd n l ->
      valid_fast_length l /\
      (fast_length_of_chunk l == n)
  )

let t x = (c:chunk x{valid_fast_length c})

let of_list_direct (l:list 'a) :
  Pure (t 'a)
    (requires (True))
    (ensures (fun r -> chunk_as_list r == l)) =
  let c: chunk _ = List (L.length l) l in
  assert_norm (chunk_as_list c == l); (* OBSERVE *)
  assert_norm (valid_fast_length c);
  c

#push-options "--fuel 1"
(* Create a [t] from a [list], but force breaking down into a tree
   such that no leaf is longer than [max_leaf_length] in length. This
   helps guarantee better performance of the [split3] operation. *)
let rec of_list_balancing (max_leaf_length:nat) (l:list 'a) :
  Pure (t 'a)
    (requires (max_leaf_length > 1))
    (ensures (fun r -> chunk_as_list r == l))
    (decreases %[L.length l]) =
  let len = L.length l in
  if len < max_leaf_length then (
    of_list_direct l
  ) else (
    let l1, l2 = L.splitAt (len / 2) l in
    LP.lemma_splitAt_append (len / 2) l;
    L.append_length l1 l2;
    Append len
      (of_list_balancing max_leaf_length l1)
      (of_list_balancing max_leaf_length l2)
  )
#pop-options

let of_list l =
  (* NOTE: the balance bound is picked arbitrarily here; should just
     be a small/medium sized integer. Too small and we slow down
     conversion to a [t], too large and we don't get much benefit out
     of [split3]. *)
  of_list_balancing 32 l

(* A convenient intermediate when converting from chunks to lists to help keep performance high.
   Denotes a single list, performed by flattening its reverse. *)
let rl_t (x:Type0) = list (list x)

let coerce (#b:Type) (#a:Type{a == b}) (x:a) : b = x

let rl_to_list (rl:rl_t 'a) : Tot (list 'a) =
  (* Both these operations are tail recursive, so should be fast enough. *)
  L.flatten (L.rev rl)

(* XXX WORKAROUND: We have to define our own version of [unzip]
   because for some reason F*'s extraction on [List.Tot.Base.unzip]
   seems to fail _hard_. Here we define it, to force a custom
   extraction, and then we set up a pattern to always connect it up to
   the [List.Tot.Base] one. We are extra careful to write a version
   that should be tail-call-optimized, even if it complicates up the
   proof required to match it up to the one in [List.Tot.Base]. *)
#push-options "--fuel 1 --ifuel 1"
let rec l_unzip_tail_call_optimized #a #b (rev1:list a) (rev2:list b) (l:list (a * b)) :
  Tot (list a * list b) (decreases %[l]) =
  match l with
  | [] -> (rev1, rev2)
  | (h1, h2) :: t ->
    l_unzip_tail_call_optimized (h1 :: rev1) (h2 :: rev2) t
let rec lemma_unzip_tco_is_list_tot_unzip_rev #a #b (rev1:list a) (rev2:list b) (l:list (a * b)) :
  Lemma
    (requires (True))
    (ensures (
        let (x, y) = l_unzip_tail_call_optimized rev1 rev2 l in
        let (l1, l2) = L.unzip l in
        (L.rev x == L.rev rev1 `L.append` l1) /\
        (L.rev y == L.rev rev2 `L.append` l2)))
    (decreases %[l]) =
  let (x, y) = l_unzip_tail_call_optimized rev1 rev2 l in
  let (l1, l2) = L.unzip l in
  calc (==) {
    (L.rev rev1 `L.append` l1);
    == { L.rev_involutive l1 }
    (L.rev rev1 `L.append` L.rev (L.rev l1));
    == { L.rev_append (L.rev l1) rev1 }
    (L.rev (L.rev l1 `L.append` rev1));
  };
  calc (==) {
    (L.rev rev2 `L.append` l2);
    == {
      (* Similar to above, but compressed down *)
      L.rev_involutive l2; L.rev_append (L.rev l2) rev2
    }
    (L.rev (L.rev l2 `L.append` rev2));
  };
  match l with
  | [] -> ()
  | (h1, h2) :: t ->
    lemma_unzip_tco_is_list_tot_unzip_rev (h1 :: rev1) (h2 :: rev2) t;
    let (xt, yt) = l_unzip_tail_call_optimized (h1 :: rev1) (h2 :: rev2) t in
    let (l1t, l2t) = L.unzip t in
    calc (==) {
      (L.rev x);
      == {}
      (L.rev xt);
      == {}
      (L.rev (h1 :: rev1) `L.append` l1t);
      == { L.rev_rev' (h1 :: rev1) }
      (L.rev' (h1 :: rev1) `L.append` l1t);
      == {}
      (L.rev' rev1 `L.append` [h1] `L.append` l1t);
      == { L.append_assoc (L.rev' rev1) [h1] l1t }
      (L.rev' rev1 `L.append` ([h1] `L.append` l1t));
      == { assert_norm ([h1] `L.append` l1t == h1 :: l1t) }
      (L.rev' rev1 `L.append` (h1 :: l1t));
      == { L.rev_rev' rev1 }
      (L.rev rev1 `L.append` l1);
    };
    calc (==) {
      (L.rev y);
      == {
        (* Similar to above, but compressed down *)
        L.rev_rev' (h2 :: rev2);
        L.append_assoc (L.rev' rev2) [h2] l2t;
        assert_norm ([h2] `L.append` l2t == h2 :: l2t);
        L.rev_rev' rev2
      }
      (L.rev rev2 `L.append` l2);
    }
let l_unzip #a #b (l:list (a * b)) : Tot (list a * list b) =
  let (x, y) = l_unzip_tail_call_optimized [] [] l in
  (L.rev x, L.rev y)
let lemma_unzip_is_list_tot_unzip #a #b (l:list (a * b)) :
  Lemma
    (requires True)
    (ensures (l_unzip l == FStar.List.Tot.Base.unzip l))
    [SMTPat (l_unzip l)] =
  lemma_unzip_tco_is_list_tot_unzip_rev [] [] l
#pop-options

let rec add_chunk_to_rl (rl:rl_t 'a) (c:chunk 'a) : Tot (rl_t 'a) (decreases %[c]) =
  allow_inversion (chunk 'a);
  match c with
  | List _ l -> l :: rl
  | Repeat n x -> l_repeat n x :: rl
  | Append _ l r ->
    add_chunk_to_rl (add_chunk_to_rl rl l) r
  | Zip #x #y _ l r ->
    let l_addn = rl_to_list (add_chunk_to_rl [] l) in
    let r_addn = rl_to_list (add_chunk_to_rl [] r) in
    let zipped = weak_l_zip l_addn r_addn in
    zipped :: rl
  | UnzipFst _ l ->
    let rl_addn = rl_to_list (add_chunk_to_rl [] l) in
    let unzipped = fst (L.unzip rl_addn) in
    unzipped :: rl
  | UnzipSnd _ l ->
    let rl_addn = rl_to_list (add_chunk_to_rl [] l) in
    let unzipped = snd (l_unzip rl_addn) in
    unzipped :: rl

let to_list l = rl_to_list (add_chunk_to_rl [] l)

#push-options "--fuel 1"
let rec lemma_flatten_append (x y:list (list 'a)) :
  Lemma
    (requires (True))
    (ensures (
        L.flatten (x `L.append` y) ==
        L.flatten x `L.append` L.flatten y)) =
  allow_inversion (list (list 'a));
  match x with
  | [] -> ()
  | hd :: tl ->
    calc (==) {
      (L.flatten (x `L.append` y));
      == {}
      (L.flatten (hd :: tl `L.append` y));
      == {}
      (hd `L.append` L.flatten (tl `L.append` y));
      == { lemma_flatten_append tl y }
      (hd `L.append` (L.flatten tl `L.append` L.flatten y));
      == { L.append_assoc hd (L.flatten tl) (L.flatten y) }
      ((hd `L.append` L.flatten tl) `L.append` L.flatten y);
      == {}
      (L.flatten (hd :: tl) `L.append` L.flatten y);
      == {}
      (L.flatten x `L.append` L.flatten y);
    }
#pop-options

#push-options "--fuel 2"
let lemma_flatten_rev_cons (hd:list 'a) (tl:list (list 'a)) :
  Lemma
    (requires (True))
    (ensures (L.flatten (L.rev (hd :: tl)) ==
              L.append
                (L.flatten (L.rev tl))
                hd)) =
  calc (==) {
    (L.flatten (L.rev (hd :: tl)));
    == { L.rev_rev' (hd :: tl); L.rev_rev' tl }
    (L.flatten (L.rev tl `L.append` [hd]));
    == { lemma_flatten_append (L.rev tl) [hd] }
    (L.flatten (L.rev tl) `L.append` L.flatten [hd]);
    == { L.append_l_nil hd }
    (L.flatten (L.rev (tl)) `L.append` hd);
  }
#pop-options

#push-options "--fuel 1"
let rec lemma_add_chunk_to_rl (rl:rl_t 'a) (c:chunk 'a) :
  Lemma
    (requires (True))
    (ensures (
        rl_to_list (add_chunk_to_rl rl c) ==
        L.append
          (rl_to_list rl)
          (chunk_as_list c)))
    (decreases %[c]) =
  allow_inversion (chunk 'a);
  allow_inversion (list 'a);
  allow_inversion (list (list 'a));
  match c with
  | List _ l ->
    lemma_flatten_rev_cons l rl
  | Repeat n x ->
    lemma_flatten_rev_cons (l_repeat n x) rl
  | Append _ l r ->
    lemma_add_chunk_to_rl rl l;
    lemma_add_chunk_to_rl (add_chunk_to_rl rl l) r;
    L.append_assoc (rl_to_list rl) (chunk_as_list l) (chunk_as_list r)
  | Zip _ l r ->
    let l_addn = rl_to_list (add_chunk_to_rl [] l) in
    let r_addn = rl_to_list (add_chunk_to_rl [] r) in
    let zipped = weak_l_zip l_addn r_addn in
    calc (==) {
      (rl_to_list (add_chunk_to_rl rl c));
      == {}
      (rl_to_list (zipped :: rl));
      == { lemma_flatten_rev_cons zipped rl }
      (rl_to_list rl `L.append` zipped);
      == {
        lemma_add_chunk_to_rl [] l;
        lemma_add_chunk_to_rl [] r
      }
      (rl_to_list rl `L.append` weak_l_zip (chunk_as_list l) (chunk_as_list r));
      == {}
      (rl_to_list rl `L.append` chunk_as_list c);
    }
  | UnzipFst _ l ->
    let rl_addn = rl_to_list (add_chunk_to_rl [] l) in
    let unzipped = fst (l_unzip rl_addn) in
    calc (==) {
      (rl_to_list (add_chunk_to_rl rl c));
      == {}
      (rl_to_list (unzipped :: rl));
      == { lemma_flatten_rev_cons unzipped rl }
      (rl_to_list rl `L.append` unzipped);
      == { lemma_add_chunk_to_rl [] l }
      (rl_to_list rl `L.append` chunk_as_list c);
    }
  | UnzipSnd _ l ->
    let rl_addn = rl_to_list (add_chunk_to_rl [] l) in
    let unzipped = snd (l_unzip rl_addn) in
    calc (==) {
      (rl_to_list (add_chunk_to_rl rl c));
      == {}
      (rl_to_list (unzipped :: rl));
      == { lemma_flatten_rev_cons unzipped rl }
      (rl_to_list rl `L.append` unzipped);
      == { lemma_add_chunk_to_rl [] l }
      (rl_to_list rl `L.append` chunk_as_list c);
    }
#pop-options

#push-options "--fuel 1"
let lemma_to_list_is_chunk_as_list (l:t 'a) :
  Lemma
    (requires (True))
    (ensures (to_list l == chunk_as_list l))
    [SMTPat (to_list l)] =
  lemma_add_chunk_to_rl [] l
#pop-options

let auto_lemma_to_of_list l =
  lemma_to_list_is_chunk_as_list (of_list l)

#push-options "--fuel 1"
let length l =
  fast_length_of_chunk l
#pop-options

#push-options "--fuel 1"
let append_unconditionally (a b:t 'a) :
  Pure (t 'a)
    (requires (True))
    (ensures (fun r -> to_list r == L.append (to_list a) (to_list b))) =
  let c: chunk _ = Append (length a + length b) a b in
  L.append_length (chunk_as_list a) (chunk_as_list b);
  assert_norm (L.append (chunk_as_list a) (chunk_as_list b) == chunk_as_list c);
  c
#pop-options

#push-options "--fuel 1 --ifuel 1"
let append a b =
  if length a = 0 then (
    b
  ) else if length b = 0 then (
    L.append_l_nil (to_list a);
    a
  ) else (
    append_unconditionally a b
  )
#pop-options

#push-options "--fuel 1"
let repeat n x = Repeat n x
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec l_zip a b =
  match a, b with
  | [], [] -> []
  | h1 :: t1, h2 :: t2 -> (h1, h2) :: l_zip t1 t2
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_weak_l_zip (l:list 'a) (r:list 'b) :
  Lemma
    (requires (L.length l == L.length r))
    (ensures (weak_l_zip l r == l_zip l r)) =
  match l, r with
  | [], [] -> ()
  | h1 :: t1, h2 :: t2 -> lemma_weak_l_zip t1 t2
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_weak_l_zip_length (l:list 'a) (r:list 'b) :
  Lemma
    (requires (L.length l == L.length r))
    (ensures (L.length (weak_l_zip l r) == L.length l)) =
  match l, r with
  | [], [] -> ()
  | h1 :: t1, h2 :: t2 ->
    lemma_weak_l_zip_length t1 t2
#pop-options

#push-options "--fuel 1"
let zip a b =
  let c: chunk _ = Zip (length a) a b in
  lemma_weak_l_zip_length (chunk_as_list a) (chunk_as_list b);
  lemma_weak_l_zip (chunk_as_list a) (chunk_as_list b);
  c
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_unzip_length (l:list ('a * 'b)) :
  Lemma
    (requires (True))
    (ensures (
        let (a, b) = L.unzip l in
        (L.length a == L.length l) /\
        (L.length b == L.length l))) =
  match l with
  | [] -> ()
  | _ :: t -> lemma_unzip_length t
#pop-options

#push-options "--fuel 1"
let unzip l =
  let c1: chunk _ = UnzipFst (length l) l in
  let c2: chunk _ = UnzipSnd (length l) l in
  lemma_unzip_length (to_list l);
  (c1, c2)
#pop-options

#push-options "--fuel 1 --ifuel 0"
let rec lemma_split3_repeat #a (n:nat) (x:a) (at_idx:nat) :
  Lemma
    (requires (at_idx < n))
    (ensures (
        let l = l_repeat n x in
        let left, mid, right = L.split3 l at_idx in
        (left == l_repeat at_idx x) /\
        (mid == x) /\
        (right == l_repeat (n - at_idx - 1) x))) =
  match n, at_idx with
  | _, 0 -> ()
  | _ -> lemma_split3_repeat (n - 1) x (at_idx - 1)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_split3_append_left #a (l1 l2:list a) (at_idx:nat) :
  Lemma
    (requires (at_idx < L.length l1))
    (ensures (
        L.append_length l1 l2;
        let left, mid, right = L.split3 (l1 `L.append` l2) at_idx in
        let left', mid', right' = L.split3 l1 at_idx in
        (left == left') /\
        (mid == mid') /\
        (right == right' `L.append` l2))) =
  match l1, at_idx with
  | [_], 0 -> ()
  | _, 0 -> ()
  | hd :: tl, _ ->
    L.append_length l1 l2;
    lemma_split3_append_left tl l2 (at_idx - 1)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_split3_append_right #a (l1 l2:list a) (at_idx:nat) :
  Lemma
    (requires (at_idx >= L.length l1 /\ at_idx < L.length (l1 `L.append` l2)))
    (ensures (
        L.append_length l1 l2;
        let left, mid, right = L.split3 (l1 `L.append` l2) at_idx in
        let left', mid', right' = L.split3 l2 (at_idx - L.length l1) in
        (left == l1 `L.append` left') /\
        (mid == mid') /\
        (right == right'))) =
  match l1 with
  | [] -> ()
  | hd :: tl ->
    L.append_length l1 l2;
    lemma_split3_append_right tl l2 (at_idx - 1)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_split3_zip #a #b (l1:list a) (l2:list b) (at_idx:nat) :
  Lemma
    (requires ((L.length l1 == L.length l2) /\ (at_idx < L.length l1)))
    (ensures (
        (at_idx < L.length (l_zip l1 l2)) /\
        (let left, mid, right = L.split3 (l_zip l1 l2) at_idx in
         let left1, mid1, right1 = L.split3 l1 at_idx in
         let left2, mid2, right2 = L.split3 l2 at_idx in
         (L.length left1 == L.length left2) /\
         (L.length right1 == L.length right2) /\
         (left == l_zip left1 left2) /\
         (mid == (mid1, mid2)) /\
         (right == l_zip right1 right2)))) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 ->
    if at_idx <> 0 then lemma_split3_zip tl1 tl2 (at_idx - 1)
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_split3_unzip #a #b (l:list (a & b)) (at_idx:nat) :
  Lemma
    (requires (at_idx < L.length l))
    (ensures (
        (L.length (fst (L.unzip l)) == L.length l) /\
        (L.length (snd (L.unzip l)) == L.length l) /\
        (let left, mid, right = L.split3 l at_idx in
         let left1, mid1, right1 = L.split3 (fst (L.unzip l)) at_idx in
         let left2, mid2, right2 = L.split3 (snd (L.unzip l)) at_idx in
         (L.unzip left == (left1, left2)) /\
         (mid == (mid1, mid2)) /\
         (L.unzip right == (right1, right2))))) =
  lemma_unzip_length l;
  match l with
  | [] -> ()
  | hd :: tl ->
    if at_idx <> 0 then lemma_split3_unzip tl (at_idx - 1)
#pop-options

#push-options "--fuel 2 --ifuel 1"
let rec split3 #a (root:t a) (at_idx:nat) =
  LP.lemma_split3_length (to_list root) at_idx;
  match root with
  | List n l ->
    let left, mid, right = L.split3 l at_idx in
    let left = List at_idx left in
    let right = List (n - at_idx - 1) right in
    (left, mid, right)
  | Repeat n x ->
    lemma_split3_repeat n x at_idx;
    (Repeat at_idx x, x, Repeat (n - at_idx - 1) x)
  | Append n l r ->
    if at_idx < fast_length_of_chunk l then (
      lemma_split3_append_left (to_list l) (to_list r) at_idx;
      let left, mid, right = split3 l at_idx in
      L.append_length (chunk_as_list right) (to_list r);
      let right = Append (n - at_idx - 1) right r in
      (left, mid, right)
    ) else (
      lemma_split3_append_right (to_list l) (to_list r) at_idx;
      let left, mid, right = split3 r (at_idx - fast_length_of_chunk l) in
      L.append_length (chunk_as_list l) (to_list left);
      let left = Append at_idx l left in
      (left, mid, right)
    )
  | Zip n l r ->
    lemma_split3_zip (to_list l) (to_list r) at_idx;
    lemma_weak_l_zip (to_list l) (to_list r);
    let left1, mid1, right1 = split3 l at_idx in
    let left2, mid2, right2 = split3 r at_idx in
    LP.lemma_split3_length (to_list l) at_idx;
    LP.lemma_split3_length (to_list r) at_idx;
    let left = Zip at_idx left1 left2 in
    let mid = (mid1, mid2) in
    let right = Zip (n - at_idx - 1) right1 right2 in
    lemma_weak_l_zip (to_list left1) (to_list left2);
    lemma_weak_l_zip (to_list right1) (to_list right2);
    (left, mid, right)
  | UnzipFst n l ->
    lemma_split3_unzip (to_list l) at_idx;
    let left, mid, right = split3 l at_idx in
    LP.lemma_split3_length (to_list l) at_idx;
    let left = UnzipFst at_idx left in
    let mid = fst mid in
    let right = UnzipFst (n - at_idx - 1) right in
    (left, mid, right)
  | UnzipSnd n l ->
    lemma_split3_unzip (to_list l) at_idx;
    let left, mid, right = split3 l at_idx in
    LP.lemma_split3_length (to_list l) at_idx;
    let left = UnzipSnd at_idx left in
    let mid = snd mid in
    let right = UnzipSnd (n - at_idx - 1) right in
    (left, mid, right)
#pop-options

#push-options "--fuel 2"
let index_and_optimize (l:t 'a) (idx:nat) =
  let left, mid, right = split3 l idx in
  let l' = append left (append (of_list [mid]) right) in
  LP.lemma_split3_index (to_list l) idx;
  LP.lemma_split3_append (to_list l) idx;
  mid, l'
#pop-options

#push-options "--fuel 2"
let modify_at (l:t 'a) (idx:nat) (f:'a -> Tot 'a) :
  Pure (t 'a)
    (requires (idx < length l))
    (ensures (fun l' ->
         let left, mid, right = L.split3 (to_list l) idx in
         to_list l' == left @ f mid :: right)) =
  let left, mid, right = split3 l idx in
  append left (append (of_list [f mid]) right)
#pop-options
