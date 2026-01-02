
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _::l' -> succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (succ n) m
 end

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

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a::l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a::l0 -> (&&) (f a) (forallb f l0)

type row = int list

type matrix = row list

type solution = int list

(** val covered_cols : matrix -> int list -> int list **)

let rec covered_cols matrix0 = function
| [] -> []
| r::rest ->
  (match nth_error matrix0 r with
   | Some row0 -> app row0 (covered_cols matrix0 rest)
   | None -> covered_cols matrix0 rest)

(** val has_duplicates : int list -> bool **)

let rec has_duplicates = function
| [] -> false
| x::rest -> if existsb ((=) x) rest then true else has_duplicates rest

(** val check_exact_cover : matrix -> int -> solution -> bool **)

let check_exact_cover matrix0 num_cols sol =
  let cols = covered_cols matrix0 sol in
  (&&) ((&&) (negb (has_duplicates cols)) ((=) (length cols) num_cols))
    (forallb (fun r -> Nat.ltb r (length matrix0)) sol)

(** val placement_cols : int -> int -> int -> int -> row **)

let placement_cols n r c v =
  (add (mul r n) c)::((add (add (mul n n) (mul r n)) (sub v (succ 0)))::(
    (add (add (mul (mul (succ (succ 0)) n) n) (mul c n)) (sub v (succ 0)))::[]))

(** val build_latin_matrix_rows : int -> int -> int -> int -> matrix **)

let rec build_latin_matrix_rows n r c v =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun v' -> (placement_cols n r c v)::(build_latin_matrix_rows n r c v'))
    v

(** val build_latin_matrix_cols : int -> int -> int -> matrix **)

let rec build_latin_matrix_cols n r c =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun c' ->
    app (build_latin_matrix_rows n r c' n) (build_latin_matrix_cols n r c'))
    c

(** val build_latin_matrix_full : int -> int -> matrix **)

let rec build_latin_matrix_full n r =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun r' ->
    app (build_latin_matrix_cols n r' n) (build_latin_matrix_full n r'))
    r

(** val build_latin_matrix : int -> matrix **)

let build_latin_matrix n =
  build_latin_matrix_full n n
