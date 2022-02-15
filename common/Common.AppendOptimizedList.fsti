module Common.AppendOptimizedList

#reset-options "--fuel 0 --ifuel 0"

module L = FStar.List.Tot

(** An append-optimized list. All time complexities of operations
    applied to this are specified in terms of the number of elements
    [n] in the list denoted by this type. *)
val t : (t:Type0) -> Type u#1

(** Convert from a standard list. Takes `O(n log n)` time. *)
val of_list : list 'a -> Tot (t 'a)

(** Convert into a standard list. Takes `O(n log n)` time. *)
val to_list : t 'a -> Tot (list 'a)

(** Automatic lemma about the conversion round trip. *)
val auto_lemma_to_of_list (l:list 'a) :
  Lemma
    (requires (True))
    (ensures (to_list (of_list l) == l))
    [SMTPat (to_list (of_list l))]

(** Length of the list denoted by [l]. Takes `O(1)` time. *)
val length : (l:t 'a) ->
  Pure nat
    (requires (True))
    (ensures (fun n -> n == L.length (to_list l)))

(** Append two lists. Takes `O(1)` time. *)
val append : (a:t 'a) -> (b:t 'a) ->
  Pure (t 'a)
    (requires (True))
    (ensures (fun r -> to_list r == L.append (to_list a) (to_list b)))

(** Convenient short-hand. *)
let cons (hd:'a) (tl:t 'a) : Tot (t 'a) = append (of_list [hd]) tl

(** Convenient short-hand. *)
let snoc (arg:(t 'a & 'a)) : Tot (t 'a) = append (fst arg) (of_list [snd arg])

(** Convenient short-hand. *)
let empty (#x:Type0) : Tot (t x) = of_list []

(** Construct a list of [n] copies of [x]. Takes `O(1)` time. *)
val repeat : n:nat -> x:'a ->
  Pure (t 'a)
    (requires (True))
    (ensures (fun r -> length r = n))

(** A high-level specification of zip *)
val l_zip : a:list 'a -> b:list 'b ->
  Pure (list ('a & 'b))
    (requires (L.length a == L.length b))
    (ensures (fun res -> L.unzip res == (a, b)))

(** Zip two lists together. Takes `O(1)` time. *)
val zip : (a:t 'a) -> (b:t 'b) ->
  Pure (t ('a & 'b))
    (requires (length a == length b))
    (ensures (fun r -> to_list r == l_zip (to_list a) (to_list b)))

(** Unzip a list of pairs. Takes `O(1)` time. *)
val unzip : (l:t ('a & 'b)) ->
  Pure (t 'a & t 'b)
    (requires (True))
    (ensures (fun (a, b) -> L.unzip (to_list l) == (to_list a, to_list b)))

(** Split a list [l] at [idx] into left, middle, and right portions.
    Takes `O(n)` time in worst case, but is expected to take amortized
    `O(log n)`. *)
val split3 : (l:t 'a) -> (idx:nat) ->
  Pure (t 'a & 'a & t 'a)
    (requires (idx < length l))
    (ensures (fun (left, mid, right) ->
         let l_left, l_mid, l_right = L.split3 (to_list l) idx in
         (l_left == to_list left) /\
         (l_mid == mid) /\
         (l_right == to_list right)))

(** Get the [idx]th element from the list [l]. Additionally, optimize
    the list to make further indexing (and other) operations faster.
    Takes `O(n)` in the worst case, but is expected to take amortized
    `O(log n)`.

    Expected usage: `let (x, l) = index l idx in ...` *)
val index_and_optimize : (l:t 'a) -> (idx:nat) ->
  Pure ('a & t 'a)
    (requires (idx < length l))
    (ensures (fun (x, l') ->
         (x == L.index (to_list l) idx) /\
         (to_list l == to_list l')))

(** Modify the [idx]th element in the list [l] using the function
    [f]. Additionally, optimize the list to make further operations
    faster. Takes `O(n)` in the worst case, but is expected to take
    amortized `O(log n)`. *)
val modify_at : (l:t 'a) -> (idx:nat) -> (f:('a -> Tot 'a)) ->
  Pure (t 'a)
    (requires (idx < length l))
    (ensures (fun l' ->
         let left, mid, right = L.split3 (to_list l) idx in
         to_list l' == left @ f mid :: right))

(** Replace the [idx]th element in the list [l] with [x].
    Additionally, optimize the list to make further operations
    faster. Takes `O(n)` in the worst case, but is expected to take
    amortized `O(log n)`.

    See [modify_at] if you want to use the pre-existing value at [idx]
    to generate [x]. *)
let update_at (l:t 'a) (idx:nat) (x:'a) :
  Pure (t 'a)
    (requires (idx < length l))
    (ensures (fun l' ->
         let left, _, right = L.split3 (to_list l) idx in
         to_list l' == left @ x :: right)) =
  modify_at l idx (fun _ -> x)
