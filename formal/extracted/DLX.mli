
val negb : bool -> bool

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val ltb : int -> int -> bool
 end

val nth_error : 'a1 list -> int -> 'a1 option

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type row = int list

type matrix = row list

type solution = int list

val covered_cols : matrix -> int list -> int list

val has_duplicates : int list -> bool

val check_exact_cover : matrix -> int -> solution -> bool

val placement_cols : int -> int -> int -> int -> row

val build_latin_matrix_rows : int -> int -> int -> int -> matrix

val build_latin_matrix_cols : int -> int -> int -> matrix

val build_latin_matrix_full : int -> int -> matrix

val build_latin_matrix : int -> matrix
