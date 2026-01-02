
type comparison =
| Eq
| Lt
| Gt

(** val add : int -> int -> int **)

let rec add = (+)

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Coq_Pos =
 struct
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op add x (Stdlib.Int.succ 0)
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val of_nat : int -> int **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n0 -> (Pos.of_succ_nat n0))
      n

  (** val gtb : int -> int -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false
 end

(** val fact_nat : int -> int **)

let rec fact_nat n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 1)
    (fun m -> Z.mul (Z.of_nat n) (fact_nat m))
    n

(** val fact_z : int -> int **)

let fact_z n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 1)
    (fun p -> fact_nat (Coq_Pos.to_nat p))
    (fun _ -> 0)
    n

(** val reduced_count_z : int -> int **)

let reduced_count_z n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 0)
    (fun p ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun p1 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> 0)
          (fun _ -> 0)
          (fun _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) 1))))))
          p1)
        (fun _ -> 1)
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p1 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> 0)
          (fun _ -> 0)
          (fun _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))))))))))))
          p1)
        (fun p1 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> 0)
          (fun _ -> 0)
          (fun _ -> ((fun p->2*p) ((fun p->2*p) 1)))
          p1)
        (fun _ -> 1)
        p0)
      (fun _ -> 1)
      p)
    (fun _ -> 0)
    n

(** val latin_count_z : int -> int **)

let latin_count_z n =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> 0)
    (fun p ->
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ ->
        if Z.gtb n 0
        then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1))) (reduced_count_z n)
        else 0)
        (fun _ ->
        if Z.gtb n 0
        then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1))) (reduced_count_z n)
        else 0)
        (fun _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1))))
        p0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ ->
        if Z.gtb n 0
        then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1))) (reduced_count_z n)
        else 0)
        (fun p1 ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ ->
          if Z.gtb n 0
          then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1)))
                 (reduced_count_z n)
          else 0)
          (fun _ ->
          if Z.gtb n 0
          then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1)))
                 (reduced_count_z n)
          else 0)
          (fun _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))))))))
          p1)
        (fun _ -> ((fun p->2*p) 1))
        p0)
      (fun _ -> 1)
      p)
    (fun _ ->
    if Z.gtb n 0
    then Z.mul (Z.mul (fact_z n) (fact_z (Z.sub n 1))) (reduced_count_z n)
    else 0)
    n

(** val stirling2_z : int -> int -> int -> int **)

let rec stirling2_z fuel n k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun fuel' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 1)
        (fun _ -> 0)
        k)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun k' ->
        Z.add
          (Z.mul (Z.of_nat (Stdlib.Int.succ k'))
            (stirling2_z fuel' n' (Stdlib.Int.succ k')))
          (stirling2_z fuel' n' k'))
        k)
      n)
    fuel

(** val stirling2 : int -> int -> int **)

let stirling2 n k =
  stirling2_z (add n (Stdlib.Int.succ 0)) n k

(** val sum_stirling_z : int -> int -> int -> int **)

let rec sum_stirling_z fuel n k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> stirling2_z fuel n 0)
    (fun k' -> Z.add (stirling2_z fuel n k) (sum_stirling_z fuel n k'))
    k

(** val bell_z : int -> int **)

let bell_z n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 1)
    (fun _ -> sum_stirling_z (add n (Stdlib.Int.succ 0)) n n)
    n

(** val mODE_STANDARD : int **)

let mODE_STANDARD =
  0

(** val mODE_MULTIPLICATION : int **)

let mODE_MULTIPLICATION =
  1

(** val mODE_MYSTERY : int **)

let mODE_MYSTERY =
  ((fun p->2*p) 1)

(** val mODE_ZERO_INCLUSIVE : int **)

let mODE_ZERO_INCLUSIVE =
  ((fun p->2*p) ((fun p->2*p) 1))

(** val mODE_NEGATIVE : int **)

let mODE_NEGATIVE =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val mODE_EXPONENT : int **)

let mODE_EXPONENT =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))

(** val mODE_MODULAR : int **)

let mODE_MODULAR =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))

(** val mODE_KILLER : int **)

let mODE_KILLER =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1))))))

(** val mODE_HINT : int **)

let mODE_HINT =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1)))))))

(** val mODE_ADAPTIVE : int **)

let mODE_ADAPTIVE =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))

(** val mODE_STORY : int **)

let mODE_STORY =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))))))

(** val mODE_BITWISE : int **)

let mODE_BITWISE =
  ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))))))))))

(** val solution_space_z : int -> int **)

let solution_space_z =
  latin_count_z
