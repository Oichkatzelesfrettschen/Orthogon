
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val add : int -> int -> int **)

let rec add = (+)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n

  (** val double : int -> int **)

  let double n =
    add n n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m

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

  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2

  (** val testbit : int -> int -> bool **)

  let rec testbit = (fun n k -> (n lsr k) land 1 = 1)

  (** val shiftl : int -> int -> int **)

  let rec shiftl = (fun n k -> n lsl k)

  (** val shiftr : int -> int -> int **)

  let rec shiftr = (fun n k -> n lsr k)

  (** val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int **)

  let rec bitwise op n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' ->
      add (if op (odd a) (odd b) then succ 0 else 0)
        (mul (succ (succ 0)) (bitwise op n' (div2 a) (div2 b))))
      n

  (** val coq_lor : int -> int -> int **)

  let coq_lor = (lor)
 end

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x::(repeat x k))
    n

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x::_ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _::l' -> nth_error l' n0)
    n

type dSF = int list

(** val dsf_is_inverse : int -> bool **)

let dsf_is_inverse entry =
  Nat.testbit entry 0

(** val dsf_is_root : int -> bool **)

let dsf_is_root entry =
  Nat.testbit entry (succ 0)

(** val dsf_parent_or_size : int -> int **)

let dsf_parent_or_size entry =
  Nat.shiftr entry (succ (succ 0))

(** val dsf_pack_root : int -> int **)

let dsf_pack_root size =
  Nat.coq_lor (Nat.shiftl size (succ (succ 0))) (succ (succ 0))

(** val dsf_pack_child : int -> bool -> int **)

let dsf_pack_child parent inverse =
  Nat.coq_lor (Nat.shiftl parent (succ (succ 0)))
    (if inverse then succ 0 else 0)

(** val dsf_init_entry : int **)

let dsf_init_entry =
  succ (succ (succ (succ (succ (succ 0)))))

(** val dsf_init : int -> dSF **)

let dsf_init size =
  repeat dsf_init_entry size

(** val dsf_get : dSF -> int -> int option **)

let dsf_get =
  nth_error

(** val list_set : 'a1 list -> int -> 'a1 -> 'a1 list **)

let rec list_set l idx v =
  match l with
  | [] -> []
  | h::t ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> v::t)
       (fun n -> h::(list_set t n v))
       idx)

(** val dsf_set : dSF -> int -> int -> dSF **)

let dsf_set =
  list_set

(** val canonify_step : dSF -> int -> bool -> ((int*bool)*bool) option **)

let canonify_step dsf idx inv =
  match dsf_get dsf idx with
  | Some entry ->
    if dsf_is_root entry
    then Some ((idx,inv),true)
    else let parent = dsf_parent_or_size entry in
         let step_inv = dsf_is_inverse entry in
         Some ((parent,(xorb inv step_inv)),false)
  | None -> None

(** val canonify_fuel : int -> dSF -> int -> bool -> (int*bool) option **)

let rec canonify_fuel fuel dsf idx inv =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun fuel' ->
    match canonify_step dsf idx inv with
    | Some p ->
      let p0,is_root = p in
      let next_idx,new_inv = p0 in
      if is_root
      then Some (next_idx,new_inv)
      else canonify_fuel fuel' dsf next_idx new_inv
    | None -> None)
    fuel

(** val edsf_canonify : dSF -> int -> (int*bool) option **)

let edsf_canonify dsf idx =
  canonify_fuel (length dsf) dsf idx false

(** val dsf_canonify : dSF -> int -> int option **)

let dsf_canonify dsf idx =
  match edsf_canonify dsf idx with
  | Some p -> let root,_ = p in Some root
  | None -> None

(** val dsf_size : dSF -> int -> int option **)

let dsf_size dsf idx =
  match dsf_canonify dsf idx with
  | Some root ->
    (match dsf_get dsf root with
     | Some entry -> Some (dsf_parent_or_size entry)
     | None -> None)
  | None -> None

(** val edsf_merge : dSF -> int -> int -> bool -> dSF option **)

let edsf_merge dsf v1 v2 inverse =
  match edsf_canonify dsf v1 with
  | Some p ->
    let r1,i1 = p in
    (match edsf_canonify dsf v2 with
     | Some p0 ->
       let r2,i2 = p0 in
       if (=) r1 r2
       then if eqb (xorb (xorb i1 i2) inverse) false then Some dsf else None
       else let final_inverse = xorb (xorb i1 i2) inverse in
            if Nat.ltb r1 r2
            then (match dsf_get dsf r1 with
                  | Some entry1 ->
                    (match dsf_get dsf r2 with
                     | Some entry2 ->
                       let size1 = dsf_parent_or_size entry1 in
                       let size2 = dsf_parent_or_size entry2 in
                       let dsf' =
                         dsf_set dsf r1 (dsf_pack_root (add size1 size2))
                       in
                       let dsf'' =
                         dsf_set dsf' r2 (dsf_pack_child r1 final_inverse)
                       in
                       Some dsf''
                     | None -> None)
                  | None -> None)
            else (match dsf_get dsf r2 with
                  | Some entry1 ->
                    (match dsf_get dsf r1 with
                     | Some entry2 ->
                       let size1 = dsf_parent_or_size entry1 in
                       let size2 = dsf_parent_or_size entry2 in
                       let dsf' =
                         dsf_set dsf r2 (dsf_pack_root (add size1 size2))
                       in
                       let dsf'' =
                         dsf_set dsf' r1 (dsf_pack_child r2 final_inverse)
                       in
                       Some dsf''
                     | None -> None)
                  | None -> None)
     | None -> None)
  | None -> None

(** val dsf_merge : dSF -> int -> int -> dSF option **)

let dsf_merge dsf v1 v2 =
  edsf_merge dsf v1 v2 false
