
(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun m' -> succ (max n' m'))
        m)
      n0

  (** val divmod : int -> int -> int -> int -> int*int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> q,u)
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::l0 -> (f a)::(map f l0)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start::(seq (succ start) len0))
    len

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x::_ -> Some x)
    (fun n1 -> match l with
               | [] -> None
               | _::l' -> nth_error l' n1)
    n0

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x::l0 -> app x (concat l0)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::l0 -> fold_left f l0 (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x::l0 -> if f x then x::(filter f l0) else filter f l0

(** val combine : 'a1 list -> 'a2 list -> ('a1*'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl -> (match l' with
              | [] -> []
              | y::tl' -> (x,y)::(combine tl tl'))

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

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

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
    iter_op Coq__1.add x (succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val succ_pos : int -> int **)

  let succ_pos n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Pos.succ p)
      n0

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.coq_lxor p q)
        m)
      n0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
      (fun _ -> 0)
      (fun p -> (fun p -> p) ((fun p->2*p) p))
      (fun p -> (fun p -> -p) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
      (fun _ -> (fun p -> p) 1)
      (fun p -> (fun p -> p) ((fun p->1+2*p) p))
      (fun p -> (fun p -> -p) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
      (fun _ -> (fun p -> -p) 1)
      (fun p -> (fun p -> p) (Pos.pred_double p))
      (fun p -> (fun p -> -p) ((fun p->1+2*p) p))
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
        (fun _ -> (fun p -> p) ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (fun p -> p) (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p -> -p) ((fun p->2*p) q))
        (fun q -> (fun p -> -p) (Pos.pred_double q))
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

  (** val eqb : int -> int -> bool **)

  let eqb = (=)

  (** val to_nat : int -> int **)

  let to_nat = (fun z -> if z < 0 then 0 else z)

  (** val of_nat : int -> int **)

  let of_nat = (fun n -> n)

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor = (lxor)

  (** val abs : int -> int **)

  let abs = abs
 end

type literal = int

type clause = literal list

type cNF = clause list

(** val var_cell_digit : int -> int -> int -> int -> int **)

let var_cell_digit n0 r c d =
  Z.of_nat (add (add (add (mul (mul r n0) n0) (mul c n0)) d) (succ 0))

(** val at_least_one_clause : int -> int -> int -> clause **)

let at_least_one_clause n0 r c =
  map (fun d -> var_cell_digit n0 r c d) (seq 0 n0)

(** val at_most_one_clauses_aux :
    int -> int -> int -> int -> int list -> clause list **)

let rec at_most_one_clauses_aux n0 r c d1 = function
| [] -> []
| d2::rest ->
  ((Z.opp (var_cell_digit n0 r c d1))::((Z.opp (var_cell_digit n0 r c d2))::[]))::
    (at_most_one_clauses_aux n0 r c d1 rest)

(** val at_most_one_clauses : int -> int -> int -> int list -> clause list **)

let rec at_most_one_clauses n0 r c = function
| [] -> []
| d::rest ->
  app (at_most_one_clauses_aux n0 r c d rest)
    (at_most_one_clauses n0 r c rest)

(** val exactly_one_cell : int -> int -> int -> cNF **)

let exactly_one_cell n0 r c =
  (at_least_one_clause n0 r c)::(at_most_one_clauses n0 r c (seq 0 n0))

(** val row_unique_aux :
    int -> int -> int -> int -> int list -> clause list **)

let rec row_unique_aux n0 r d c1 = function
| [] -> []
| c2::rest ->
  ((Z.opp (var_cell_digit n0 r c1 d))::((Z.opp (var_cell_digit n0 r c2 d))::[]))::
    (row_unique_aux n0 r d c1 rest)

(** val row_unique_digit : int -> int -> int -> int list -> clause list **)

let rec row_unique_digit n0 r d = function
| [] -> []
| c::rest -> app (row_unique_aux n0 r d c rest) (row_unique_digit n0 r d rest)

(** val row_unique : int -> int -> int -> cNF **)

let row_unique n0 r d =
  row_unique_digit n0 r d (seq 0 n0)

(** val col_unique_aux :
    int -> int -> int -> int -> int list -> clause list **)

let rec col_unique_aux n0 c d r1 = function
| [] -> []
| r2::rest ->
  ((Z.opp (var_cell_digit n0 r1 c d))::((Z.opp (var_cell_digit n0 r2 c d))::[]))::
    (col_unique_aux n0 c d r1 rest)

(** val col_unique_digit : int -> int -> int -> int list -> clause list **)

let rec col_unique_digit n0 c d = function
| [] -> []
| r::rest -> app (col_unique_aux n0 c d r rest) (col_unique_digit n0 c d rest)

(** val col_unique : int -> int -> int -> cNF **)

let col_unique n0 c d =
  col_unique_digit n0 c d (seq 0 n0)

(** val latin_cnf : int -> cNF **)

let latin_cnf n0 =
  app
    (flat_map (fun r ->
      flat_map (fun c -> exactly_one_cell n0 r c) (seq 0 n0)) (seq 0 n0))
    (app
      (flat_map (fun r -> flat_map (fun d -> row_unique n0 r d) (seq 0 n0))
        (seq 0 n0))
      (flat_map (fun c -> flat_map (fun d -> col_unique n0 c d) (seq 0 n0))
        (seq 0 n0)))

type cell = int*int

type cageOp =
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpXor
| OpMod

type cage = { cage_cells : cell list; cage_op : cageOp; cage_target : int }

(** val all_tuples : int -> int -> int list list **)

let rec all_tuples n0 k =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> []::[])
    (fun k' ->
    flat_map (fun t -> map (fun v -> v::t) (seq (succ 0) n0))
      (all_tuples n0 k'))
    k

(** val eval_op : cageOp -> int -> int list -> int option **)

let eval_op op n0 vals =
  match op with
  | OpAdd -> Some (fold_left (fun a b -> Z.add a (Z.of_nat b)) vals 0)
  | OpSub ->
    (match vals with
     | [] -> None
     | a::l ->
       (match l with
        | [] -> None
        | b::l0 ->
          (match l0 with
           | [] ->
             let diff = Z.sub (Z.of_nat a) (Z.of_nat b) in Some (Z.abs diff)
           | _::_ -> None)))
  | OpMul ->
    Some (fold_left (fun a b -> Z.mul a (Z.of_nat b)) vals ((fun p -> p) 1))
  | OpDiv ->
    (match vals with
     | [] -> None
     | a::l ->
       (match l with
        | [] -> None
        | b::l0 ->
          (match l0 with
           | [] ->
             if (=) (Nat.modulo a b) 0
             then Some (Z.of_nat (Nat.div a b))
             else if (=) (Nat.modulo b a) 0
                  then Some (Z.of_nat (Nat.div b a))
                  else None
           | _::_ -> None)))
  | OpXor -> Some (fold_left (fun a b -> Z.coq_lxor a (Z.of_nat b)) vals 0)
  | OpMod ->
    let sum = fold_left Nat.add vals 0 in Some (Z.of_nat (Nat.modulo sum n0))

(** val valid_tuples : int -> cage -> int list list **)

let valid_tuples n0 cage0 =
  let tuples = all_tuples n0 (length cage0.cage_cells) in
  filter (fun t ->
    match eval_op cage0.cage_op n0 t with
    | Some v -> Z.eqb v cage0.cage_target
    | None -> false) tuples

(** val tuple_aux_var : int -> int -> int -> int **)

let tuple_aux_var base_var cage_id tuple_id =
  Z.of_nat
    (add
      (add
        (add base_var
          (mul cage_id (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
            (succ
            0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        tuple_id)
      (succ 0))

(** val encode_tuple_forward : int -> cell list -> int list -> int -> cNF **)

let encode_tuple_forward n0 cells tuple aux =
  map (fun cv ->
    let c,v = cv in
    let r,col = c in
    (Z.opp aux)::((var_cell_digit n0 r col (sub v (succ 0)))::[]))
    (combine cells tuple)

(** val encode_tuple_backward :
    int -> cell list -> int list -> int -> clause **)

let encode_tuple_backward n0 cells tuple aux =
  aux::(map (fun cv ->
         let c,v = cv in
         let r,col = c in Z.opp (var_cell_digit n0 r col (sub v (succ 0))))
         (combine cells tuple))

(** val encode_cage : int -> int -> int -> cage -> cNF **)

let encode_cage n0 base_var cage_id cage0 =
  let tuples = valid_tuples n0 cage0 in
  let cells = cage0.cage_cells in
  let aux_vars =
    map (fun i -> tuple_aux_var base_var cage_id i) (seq 0 (length tuples))
  in
  let forwards =
    flat_map (fun ia ->
      let i,aux = ia in
      (match nth_error tuples i with
       | Some t -> encode_tuple_forward n0 cells t aux
       | None -> []))
      (combine (seq 0 (length aux_vars)) aux_vars)
  in
  let backwards =
    map (fun ia ->
      let i,aux = ia in
      (match nth_error tuples i with
       | Some t -> encode_tuple_backward n0 cells t aux
       | None -> []))
      (combine (seq 0 (length aux_vars)) aux_vars)
  in
  aux_vars::(app forwards backwards)

(** val clause_to_dimacs : clause -> int list **)

let clause_to_dimacs c =
  app c (0::[])

(** val cnf_to_dimacs : cNF -> int list list **)

let cnf_to_dimacs f =
  map clause_to_dimacs f

(** val count_variables : cNF -> int **)

let count_variables f =
  let all_lits = concat f in
  let abs_lits = map (fun l -> Z.to_nat (Z.abs l)) all_lits in
  (match abs_lits with
   | [] -> 0
   | _::_ -> fold_left Nat.max abs_lits 0)

(** val count_clauses : cNF -> int **)

let count_clauses =
  length
