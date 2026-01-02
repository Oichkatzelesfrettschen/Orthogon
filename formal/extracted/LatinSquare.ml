
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

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

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

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

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b
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

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x::l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b::l0 -> fold_left f l0 (f a0 b)

type cell = int*int

type constraint0 =
| CellFilled of int * int
| RowValue of int * int
| ColValue of int * int

type placement = { pl_row : int; pl_col : int; pl_val : int }

(** val placement_constraints : int -> placement -> constraint0 list **)

let placement_constraints _ p =
  (CellFilled (p.pl_row, p.pl_col))::((RowValue (p.pl_row,
    p.pl_val))::((ColValue (p.pl_col, p.pl_val))::[]))

(** val all_placements : int -> placement list **)

let all_placements n =
  flat_map (fun r ->
    flat_map (fun c ->
      map (fun v -> { pl_row = r; pl_col = c; pl_val = v }) (seq (succ 0) n))
      (seq 0 n))
    (seq 0 n)

type cageOp =
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpXor
| OpMod

type cage = { cage_cells : cell list; cage_op : cageOp; cage_target : int }

(** val eval_cage : int -> cage -> int list -> int option **)

let eval_cage n cage0 values =
  match cage0.cage_op with
  | OpAdd -> Some (fold_left Nat.add values 0)
  | OpSub ->
    (match values with
     | [] -> None
     | a::l ->
       (match l with
        | [] -> None
        | b::l0 ->
          (match l0 with
           | [] -> Some (if (<=) a b then sub b a else sub a b)
           | _::_ -> None)))
  | OpMul -> Some (fold_left Nat.mul values (succ 0))
  | OpDiv ->
    (match values with
     | [] -> None
     | a::l ->
       (match l with
        | [] -> None
        | b::l0 ->
          (match l0 with
           | [] ->
             if (=) (Nat.modulo a b) 0
             then Some (Nat.div a b)
             else if (=) (Nat.modulo b a) 0 then Some (Nat.div b a) else None
           | _::_ -> None)))
  | OpXor -> Some (fold_left Nat.coq_lxor values 0)
  | OpMod -> Some (Nat.modulo (fold_left Nat.add values 0) n)
