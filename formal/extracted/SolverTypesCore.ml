
type __ = Obj.t

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



(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
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

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p
 end

module N =
 struct
  (** val succ_pos : int -> int **)

  let succ_pos n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Pos.succ p)
      n0

  (** val coq_lor : int -> int -> int **)

  let coq_lor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> (Pos.coq_lor p q))
        m)
      n0

  (** val ldiff : int -> int -> int **)

  let ldiff n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.ldiff p q)
        m)
      n0
 end

module Z =
 struct
  (** val eqb : int -> int -> bool **)

  let eqb = (=)

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun fZ fPos fNeg z -> if z = 0 then fZ () else if z > 0 then fPos z else fNeg (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (N.ldiff b0 (Pos.pred_N a0)))
        (fun b0 -> (fun p -> -p)
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a
 end

type digit = int

type cell = int*int

type cell_in_bounds = __

(** val cell_to_index : int -> cell -> int **)

let cell_to_index n0 = function
| row,col -> add (mul row n0) col

(** val index_to_cell : int -> int -> cell **)

let index_to_cell n0 idx =
  (Nat.div idx n0),(Nat.modulo idx n0)

type gridList = digit list

type possibilityCube = bool list

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

(** val clue_op : clue -> cageOp **)

let clue_op c =
  c.clue_op

(** val clue_value : clue -> int **)

let clue_value c =
  c.clue_value

type cage = { cage_cells : cell list; cage_clue : clue }

(** val cage_cells : cage -> cell list **)

let cage_cells c =
  c.cage_cells

(** val cage_clue : cage -> clue **)

let cage_clue c =
  c.cage_clue

type difficulty =
| DiffEasy
| DiffNormal
| DiffHard
| DiffExtreme
| DiffUnreasonable
| DiffLudicrous
| DiffIncomprehensible

(** val diff_to_nat : difficulty -> int **)

let diff_to_nat = function
| DiffEasy -> 0
| DiffNormal -> succ 0
| DiffHard -> succ (succ 0)
| DiffExtreme -> succ (succ (succ 0))
| DiffUnreasonable -> succ (succ (succ (succ 0)))
| DiffLudicrous -> succ (succ (succ (succ (succ 0))))
| DiffIncomprehensible -> succ (succ (succ (succ (succ (succ 0)))))

(** val diff_leb : difficulty -> difficulty -> bool **)

let diff_leb d1 d2 =
  (<=) (diff_to_nat d1) (diff_to_nat d2)

type modeFlags = int

(** val mODE_STANDARD : int **)

let mODE_STANDARD =
  0

(** val mODE_MULTIPLICATION : int **)

let mODE_MULTIPLICATION =
  (fun p -> p) 1

(** val mODE_MYSTERY : int **)

let mODE_MYSTERY =
  (fun p -> p) ((fun p->2*p) 1)

(** val mODE_ZERO_INCLUSIVE : int **)

let mODE_ZERO_INCLUSIVE =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) 1))

(** val mODE_NEGATIVE : int **)

let mODE_NEGATIVE =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))

(** val mODE_EXPONENT : int **)

let mODE_EXPONENT =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))

(** val mODE_MODULAR : int **)

let mODE_MODULAR =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) 1)))))

(** val mODE_KILLER : int **)

let mODE_KILLER =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1))))))

(** val mODE_BITWISE : int **)

let mODE_BITWISE =
  (fun p -> p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->2*p) ((fun p->2*p) 1)))))))))))

(** val has_mode : modeFlags -> int -> bool **)

let has_mode flags mode =
  negb (Z.eqb (Z.coq_land flags mode) 0)
