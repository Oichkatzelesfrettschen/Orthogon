
type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val pow : int -> int -> int
 end

val fact : int -> int

val latin_count : int -> int

val reduced_count : int -> int

val stirling2 : int -> int -> int

val sum_stirling : int -> int -> int

val bell : int -> int

val solution_space : int -> int

val max_ambiguity_standard : int -> int -> int

val max_ambiguity_bitwise : int -> int -> int

val mODE_KILLER : int

val mODE_BITWISE : int

val mODE_MODULAR : int

val auto_upgrade_modes : int -> int -> int

val mODE_STANDARD : int

val mODE_MULTIPLICATION : int

val mODE_MYSTERY : int

val mODE_ZERO_INCLUSIVE : int

val mODE_NEGATIVE : int

val mODE_EXPONENT : int

val mODE_MODULAR0 : int

val mODE_KILLER0 : int

val mODE_HINT : int

val mODE_ADAPTIVE : int

val mODE_STORY : int

val mODE_BITWISE0 : int

type gameMode =
| Standard
| MultiplicationOnly
| Mystery
| ZeroInclusive
| NegativeNumbers
| Exponent
| Modular
| Killer
| HintMode
| Adaptive
| Story
| Bitwise
| Retro8Bit

val mode_to_flags : gameMode -> int

type flavor =
| Classik
| Kenning

val classik_modes : gameMode list

val kenning_modes : gameMode list

val mode_available : flavor -> gameMode -> bool
