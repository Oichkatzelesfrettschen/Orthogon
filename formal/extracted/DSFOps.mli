
val xorb : bool -> bool -> bool

val negb : bool -> bool

val length : 'a1 list -> int

val add : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val double : int -> int

  val mul : int -> int -> int

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val div2 : int -> int

  val testbit : int -> int -> bool

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_lor : int -> int -> int
 end

val repeat : 'a1 -> int -> 'a1 list

val nth_error : 'a1 list -> int -> 'a1 option

type dSF = int list

val dsf_is_inverse : int -> bool

val dsf_is_root : int -> bool

val dsf_parent_or_size : int -> int

val dsf_pack_root : int -> int

val dsf_pack_child : int -> bool -> int

val dsf_init_entry : int

val dsf_init : int -> dSF

val dsf_get : dSF -> int -> int option

val list_set : 'a1 list -> int -> 'a1 -> 'a1 list

val dsf_set : dSF -> int -> int -> dSF

val canonify_step : dSF -> int -> bool -> ((int*bool)*bool) option

val canonify_fuel : int -> dSF -> int -> bool -> (int*bool) option

val edsf_canonify : dSF -> int -> (int*bool) option

val dsf_canonify : dSF -> int -> int option

val dsf_size : dSF -> int -> int option

val edsf_merge : dSF -> int -> int -> bool -> dSF option

val dsf_merge : dSF -> int -> int -> dSF option
