module Common.Print

open FStar.String
open FStar.Char
open FStar.List.Tot

open Semantics.Common.FunctionInfo

let op_Plus_Plus a b = concat "" [a; b]

let nat_to_hex (n:nat) =
  let rem_to_hex (n:nat{n < 16}) =
    match n with
    | 0 -> "0"
    | 1 -> "1"
    | 2 -> "2"
    | 3 -> "3"
    | 4 -> "4"
    | 5 -> "5"
    | 6 -> "6"
    | 7 -> "7"
    | 8 -> "8"
    | 9 -> "9"
    | 10 -> "a"
    | 11 -> "b"
    | 12 -> "c"
    | 13 -> "d"
    | 14 -> "e"
    | 15 -> "f"
  in
  let rec nat_to_hex_ (n:nat) (l:list (n:nat{n < 16})): Tot (list (n:nat{n < 16})) =
    if n = 0 then l else nat_to_hex_ (n `op_Division` 16) ((n `op_Modulus` 16) :: l)
  in
  let l = nat_to_hex_ n [] in
  match l with
  | [] -> "00"
  | _ ->
    let s = concat "" (map rem_to_hex l) in
    if (length l) `op_Modulus` 2 = 0 then
      s
    else
      "0" ++ s

let nat_to_str (n:nat) = "0x" ++ (nat_to_hex n)

let int_to_str (n:int) = if n < 0 then ("-" ++ nat_to_str (-n)) else nat_to_str n

let enum (l:list 'a): Tot (list (nat * 'a)) =
  let rec enum_ (xs:list 'a) (i:nat): Tot (list (nat * 'a)) =
    match xs with
    | [] -> []
    | x :: xs -> (i, x) :: (enum_ xs (i + 1))
  in
  enum_ l 0

let enummap f xs =
  let exs = enum (map f xs) in
  let map_exs = map(fun (n, s) -> (nat_to_str n) ++ ": " ++ s) exs in
  concat "\n" map_exs

let finfo_to_str finfo =
  "nargs: " ++ (nat_to_str finfo.arg_count) ++ " nret: " ++ (nat_to_str finfo.ret_count)

let name_to_str (ns:list int) =
  let ns' = map (fun n -> char_of_int (n `op_Modulus` (pow2 21))) ns in
  string_of_list ns'
