
(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow = (fun b e ->
  let rec pow_aux acc b e =
    if e = 0 then acc
    else pow_aux (acc * b) b (e - 1)
  in pow_aux 1 b e)
 end

(** val fact_aux : int -> int -> int **)

let rec fact_aux acc n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun m -> fact_aux (mul n acc) m)
    n

(** val fact : int -> int **)

let fact n =
  fact_aux (Stdlib.Int.succ 0) n

(** val stirling2 : int -> int -> int **)

let rec stirling2 n k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun _ -> 0)
      k)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun k' ->
      add (mul (Stdlib.Int.succ k') (stirling2 n' (Stdlib.Int.succ k')))
        (stirling2 n' k'))
      k)
    n

(** val sum_stirling : int -> int -> int **)

let rec sum_stirling n k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> stirling2 n 0)
    (fun k' -> add (stirling2 n k) (sum_stirling n k'))
    k

(** val bell : int -> int **)

let bell n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Stdlib.Int.succ 0)
    (fun _ -> sum_stirling n n)
    n

(** val max_ambiguity_std : int -> int -> int **)

let max_ambiguity_std n cage_size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> fact cage_size)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> sub n (Stdlib.Int.succ 0))
        (fun _ -> fact cage_size)
        n1)
      n0)
    cage_size

(** val max_ambiguity_bit : int -> int -> int **)

let max_ambiguity_bit n cage_size =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nat.pow n cage_size)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun _ -> Nat.pow n cage_size)
        n1)
      n0)
    cage_size
