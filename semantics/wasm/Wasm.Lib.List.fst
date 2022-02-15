(**
Helper functions for lists.

@summary List helpers.
*)
module Wasm.Lib.List

open Wasm.Optr

let __lfail = Left "list"

// Note: some of these are rewritten a bit
let rec make (n:nat) x =
  if n = 0 then [] else x :: make (n - 1) x

val table: nat -> (nat -> Tot 'a) -> Tot (list 'a)
let table (n:nat) f =
  let rec table' (n:nat) (f:nat -> Tot 'a) (xs:list 'a) =
    if n = 0 then xs else table' (n - 1) f (f (n - 1) :: xs)
  in table' n f []

val take: int -> list 'a -> Tot (optr (list 'a))
let rec take n xs =
  match n, xs with
  | 0, _ -> Right []
  | n, x :: xs' ->
    if n > 0 then
      o_fmap (fun x' -> x :: x') (take (n - 1) xs')
    else
      __lfail
  | _ -> __lfail

val drop: nat -> list 'a -> Tot (optr (list 'a))
let rec drop n xs =
  match n, xs with
  | 0, _ -> Right xs
  | n, _ :: xs' ->
    if n > 0 then
      drop (n - 1) xs'
    else
      __lfail
  | _ -> __lfail

val last: list 'a -> Tot (optr 'a)
let rec last xs =
  match xs with
  | x :: [] -> Right x
  | _ :: xs -> last xs
  | [] -> __lfail

val split_last: list 'a -> Tot (optr ((list 'a) * 'a))
let rec split_last xs =
  match xs with
  | x :: [] -> Right ([], x)
  | x :: xs ->
    let r = split_last xs in
    (match r with
     | Left _ -> __lfail
     | Right (ys, y) -> Right (x :: ys, y))
  | [] -> __lfail

val index_where: ('a -> Tot bool) -> list 'a -> Tot (option nat)
let index_where p xs =
  let rec index_where' (p:'a -> Tot bool) (xs:list 'a) (i:nat) =
    match xs with
    | [] -> None
    | x :: xs' ->
      if p x then
        Some i
      else
        index_where' p xs' (i + 1)
  in index_where' p xs 0

let index_of (#a:eqtype) (x:a) (xs:list a) = index_where (fun c -> c = x) xs

val map_filter: ('a -> Tot (option 'b)) -> list 'a -> Tot (list 'b)
let rec map_filter f xs =
  match xs with
  | [] -> []
  | x :: xs ->
    (match f x with
     | None -> map_filter f xs
     | Some y -> y :: map_filter f xs
    )

val map_ex: ('a -> Tot (optr 'b)) -> list 'a -> Tot (optr (list 'b))
let rec map_ex f xs =
  match xs with
  | [] -> Right []
  | x :: xs ->
    (match f x with
     | Left y -> Left y
     | Right y -> o_fmap (fun x' -> y :: x') (map_ex f xs)
    )

val fold_right2: ('a -> 'b -> 'c -> Tot 'c)
                 -> (l1: list 'a)
                 -> (l2: (list 'b){List.Tot.length l1 = List.Tot.length l2})
                 -> 'c
                 -> Tot 'c
let rec fold_right2 f l1 l2 acc =
  match l1, l2 with
  | [], [] -> acc
  | a :: la, b :: lb -> f a b (fold_right2 f la lb acc)
