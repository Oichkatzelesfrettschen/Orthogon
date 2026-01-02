
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y



(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

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

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> succ (max n' m'))
        m)
      n

  (** val min : int -> int -> int **)

  let rec min n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> 0)
        (fun m' -> succ (min n' m'))
        m)
      n

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val odd : int -> bool **)

  let odd n =
    negb (even n)

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

  (** val gcd : int -> int -> int **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (succ a')) (succ a'))
      a

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then succ 0 else 0)
        (mul (succ (succ 0)) (bitwise op n' (div2 a) (div2 b))))
      n

  (** val coq_land : int -> int -> int **)

  let coq_land = (land)

  (** val coq_lor : int -> int -> int **)

  let coq_lor = (lor)

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor = (lxor)

  (** val lcm : int -> int -> int **)

  let lcm a b =
    mul a (div b (gcd a b))
 end

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::l0 -> fold_left f l0 (f a0 b)

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

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val eqb : int -> int -> bool **)

  let eqb = (=)

  (** val of_nat : int -> int **)

  let of_nat = (fun n -> n)
 end

type cell = int*int

type cageOp =
| OpAdd
| OpXor
| OpMul
| OpAnd
| OpSub
| OpOr
| OpDiv
| OpExp
| OpMod
| OpGcd
| OpLcm

type clue = { clue_op : cageOp; clue_value : int }

type cage = { cage_cells : cell list; cage_clue : clue }

(** val gcd0 : int -> int -> int **)

let gcd0 =
  Nat.gcd

(** val lcm0 : int -> int -> int **)

let lcm0 =
  Nat.lcm

(** val pow : int -> int -> int **)

let rec pow base exp =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> succ 0)
    (fun e' -> mul base (pow base e'))
    exp

(** val fold_add : int list -> int **)

let fold_add digits =
  fold_left Nat.add digits 0

(** val fold_mul : int list -> int **)

let fold_mul digits =
  fold_left Nat.mul digits (succ 0)

(** val fold_xor : int list -> int **)

let fold_xor digits =
  fold_left Nat.coq_lxor digits 0

(** val fold_and : int list -> int **)

let fold_and = function
| [] -> 0
| d::ds -> fold_left Nat.coq_land ds d

(** val fold_or : int list -> int **)

let fold_or digits =
  fold_left Nat.coq_lor digits 0

(** val fold_gcd : int list -> int **)

let fold_gcd = function
| [] -> 0
| d::ds -> fold_left gcd0 ds d

(** val fold_lcm : int list -> int **)

let fold_lcm = function
| [] -> succ 0
| d::ds -> fold_left lcm0 ds d

(** val eval_add : int list -> int option **)

let eval_add digits =
  Some (fold_add digits)

(** val eval_mul : int list -> int option **)

let eval_mul digits =
  Some (fold_mul digits)

(** val eval_sub : int list -> int option **)

let eval_sub = function
| [] -> None
| a::l ->
  (match l with
   | [] -> None
   | b::l0 ->
     (match l0 with
      | [] -> Some (sub (Nat.max a b) (Nat.min a b))
      | _::_ -> None))

(** val eval_div : int list -> int option **)

let eval_div = function
| [] -> None
| a::l ->
  (match l with
   | [] -> None
   | b::l0 ->
     (match l0 with
      | [] ->
        let larger = Nat.max a b in
        let smaller = Nat.min a b in
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> None)
           (fun _ ->
           if (=) (modulo larger smaller) 0
           then Some (div larger smaller)
           else None)
           smaller)
      | _::_ -> None))

(** val eval_exp : int list -> int option **)

let eval_exp = function
| [] -> None
| a::l ->
  (match l with
   | [] -> None
   | b::l0 ->
     (match l0 with
      | [] ->
        let base = Nat.min a b in
        let exponent = Nat.max a b in Some (pow base exponent)
      | _::_ -> None))

(** val eval_mod : int list -> int option **)

let eval_mod = function
| [] -> None
| a::l ->
  (match l with
   | [] -> None
   | b::l0 ->
     (match l0 with
      | [] ->
        let larger = Nat.max a b in
        let smaller = Nat.min a b in
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> None)
           (fun _ -> Some (modulo larger smaller))
           smaller)
      | _::_ -> None))

(** val eval_xor : int list -> int option **)

let eval_xor digits =
  Some (fold_xor digits)

(** val eval_and : int list -> int option **)

let eval_and digits =
  Some (fold_and digits)

(** val eval_or : int list -> int option **)

let eval_or digits =
  Some (fold_or digits)

(** val eval_gcd : int list -> int option **)

let eval_gcd digits =
  Some (fold_gcd digits)

(** val eval_lcm : int list -> int option **)

let eval_lcm digits =
  Some (fold_lcm digits)

(** val eval_cage_op : cageOp -> int list -> int option **)

let eval_cage_op op digits =
  match op with
  | OpAdd -> eval_add digits
  | OpXor -> eval_xor digits
  | OpMul -> eval_mul digits
  | OpAnd -> eval_and digits
  | OpSub -> eval_sub digits
  | OpOr -> eval_or digits
  | OpDiv -> eval_div digits
  | OpExp -> eval_exp digits
  | OpMod -> eval_mod digits
  | OpGcd -> eval_gcd digits
  | OpLcm -> eval_lcm digits

(** val cage_satisfiedb : cage -> int list -> bool **)

let cage_satisfiedb cage0 digits =
  match eval_cage_op cage0.cage_clue.clue_op digits with
  | Some v -> Z.eqb (Z.of_nat v) cage0.cage_clue.clue_value
  | None -> false

type opClass = { oc_op : cageOp; oc_binary_only : bool;
                 oc_commutative : bool; oc_associative : bool;
                 oc_identity : int option }

(** val classify_op : cageOp -> opClass **)

let classify_op = function
| OpMul ->
  { oc_op = OpMul; oc_binary_only = false; oc_commutative = true;
    oc_associative = true; oc_identity = (Some (succ 0)) }
| OpAnd ->
  { oc_op = OpAnd; oc_binary_only = false; oc_commutative = true;
    oc_associative = true; oc_identity = None }
| OpSub ->
  { oc_op = OpSub; oc_binary_only = true; oc_commutative = true;
    oc_associative = false; oc_identity = None }
| OpDiv ->
  { oc_op = OpDiv; oc_binary_only = true; oc_commutative = true;
    oc_associative = false; oc_identity = None }
| OpExp ->
  { oc_op = OpExp; oc_binary_only = true; oc_commutative = false;
    oc_associative = false; oc_identity = None }
| OpMod ->
  { oc_op = OpMod; oc_binary_only = true; oc_commutative = false;
    oc_associative = false; oc_identity = None }
| OpGcd ->
  { oc_op = OpGcd; oc_binary_only = false; oc_commutative = true;
    oc_associative = true; oc_identity = None }
| OpLcm ->
  { oc_op = OpLcm; oc_binary_only = false; oc_commutative = true;
    oc_associative = true; oc_identity = (Some (succ 0)) }
| x ->
  { oc_op = x; oc_binary_only = false; oc_commutative = true;
    oc_associative = true; oc_identity = (Some 0) }
