import LeanTrominoes.Complexity
import LeanTrominoes.Periodic
import LeanTrominoes.StripFrontierSpace
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# Binary input-encoding bounds

This file proves quantitative properties of Mathlib's binary natural-number
encoding and standard pairing-based list encoding.  It specializes them to
the project's `PeriodicStrip` encoding, showing that the strip period's
binary logarithm and motif length are bounded by the encoded input length.
Together with the sparse frontier-state count, this gives a linear bound on
the Savitch recursion depth.
-/

open Computability

namespace LeanTrominoes
namespace EncodingBounds

theorem posNum_lt_pow_encodePosNum_length (number : PosNum) :
    (number : Nat) < 2 ^ (encodePosNum number).length := by
  induction number with
  | one => decide
  | bit1 number ih =>
      simp only [encodePosNum, List.length_cons, pow_succ]
      change (number : Nat) + (number : Nat) + 1 <
        2 ^ (encodePosNum number).length * 2
      omega
  | bit0 number ih =>
      simp only [encodePosNum, List.length_cons, pow_succ]
      change (number : Nat) + (number : Nat) <
        2 ^ (encodePosNum number).length * 2
      omega

theorem nat_lt_pow_encodeNat_length (number : Nat) :
    number < 2 ^ (encodeNat number).length := by
  rw [← Num.to_of_nat number]
  generalize (number : Num) = encoded
  cases encoded with
  | zero => simp [encodeNat, encodeNum]
  | pos positive =>
      simpa [encodeNat, encodeNum] using
        posNum_lt_pow_encodePosNum_length positive

theorem two_mul_right_le_pair_succ (left right : Nat) :
    2 * right ≤ Nat.pair left right + 1 := by
  rw [Nat.pair]
  split_ifs with less
  · nlinarith
  · have rightLe : right ≤ left := by omega
    have squareNonnegative : 0 ≤ left * left := Nat.zero_le _
    omega

theorem pow_length_tail_le_encode_list {α : Type*} [Encodable α]
    (head : α) (tail : List α) :
    2 ^ tail.length ≤ Encodable.encode (head :: tail) := by
  induction tail generalizing head with
  | nil =>
      simp only [List.length_nil, pow_zero, Encodable.encode_list_cons,
        Encodable.encode_list_nil]
      omega
  | cons next tail ih =>
      rw [Encodable.encode_list_cons, List.length_cons, pow_succ]
      calc
        2 ^ tail.length * 2 ≤
            Encodable.encode (next :: tail) * 2 :=
          Nat.mul_le_mul_right 2 (ih next)
        _ = 2 * Encodable.encode (next :: tail) := by omega
        _ ≤ Nat.pair (Encodable.encode head)
              (Encodable.encode (next :: tail)) + 1 :=
          two_mul_right_le_pair_succ _ _

theorem list_length_le_encodeNat_encode_length {α : Type*} [Encodable α]
    (values : List α) :
    values.length ≤ (encodeNat (Encodable.encode values)).length := by
  cases values with
  | nil => simp
  | cons head tail =>
      have powers :
          2 ^ tail.length <
            2 ^ (encodeNat (Encodable.encode (head :: tail))).length :=
        (pow_length_tail_le_encode_list head tail).trans_lt
          (nat_lt_pow_encodeNat_length
            (Encodable.encode (head :: tail)))
      have lengths :=
        (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp powers
      simp only [List.length_cons]
      omega

end EncodingBounds

namespace PeriodicStrip

theorem period_le_encode (periodicStrip : PeriodicStrip) :
    periodicStrip.period ≤ Encodable.encode periodicStrip := by
  change periodicStrip.period ≤
    Encodable.encode
      (periodicStrip.width, periodicStrip.period, periodicStrip.motif)
  simp only [Encodable.encode_prod_val]
  exact (Nat.left_le_pair _ _).trans (Nat.right_le_pair _ _)

theorem motif_encode_le_encode (periodicStrip : PeriodicStrip) :
    Encodable.encode periodicStrip.motif ≤
      Encodable.encode periodicStrip := by
  change Encodable.encode periodicStrip.motif ≤
    Encodable.encode
      (periodicStrip.width, periodicStrip.period, periodicStrip.motif)
  simp only [Encodable.encode_prod_val]
  exact (Nat.right_le_pair _ _).trans (Nat.right_le_pair _ _)

theorem clog_period_le_encoding_length (periodicStrip : PeriodicStrip) :
    Nat.clog 2 periodicStrip.period ≤
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length := by
  change Nat.clog 2 periodicStrip.period ≤
    (encodeNat (Encodable.encode periodicStrip)).length
  apply Nat.clog_le_of_le_pow
  exact (period_le_encode periodicStrip).trans
    (EncodingBounds.nat_lt_pow_encodeNat_length
      (Encodable.encode periodicStrip)).le

theorem motif_length_le_encoding_length (periodicStrip : PeriodicStrip) :
    periodicStrip.motif.length ≤
      ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length := by
  change periodicStrip.motif.length ≤
    (encodeNat (Encodable.encode periodicStrip)).length
  cases motifEq : periodicStrip.motif with
  | nil =>
      exact Nat.zero_le _
  | cons head tail =>
      have motifBound := motif_encode_le_encode periodicStrip
      rw [motifEq] at motifBound
      have powers :
          2 ^ tail.length <
            2 ^ (encodeNat (Encodable.encode periodicStrip)).length :=
        (EncodingBounds.pow_length_tail_le_encode_list head tail).trans
          motifBound |>.trans_lt
            (EncodingBounds.nat_lt_pow_encodeNat_length
              (Encodable.encode periodicStrip))
      have lengths :=
        (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp powers
      simp only [List.length_cons]
      omega

end PeriodicStrip

namespace PeriodicStrip.WindowState

theorem savitchDepth_le_encoding_length (periodicStrip : PeriodicStrip) :
    FiniteState.savitchDepth (WindowState periodicStrip) ≤
      21 * ((Complexity.primcodableFinEncoding PeriodicStrip).encode
        periodicStrip).length + 1 := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  calc
    FiniteState.savitchDepth (WindowState periodicStrip) ≤
        Nat.clog 2 periodicStrip.period +
          20 * periodicStrip.motif.toFinset.card + 1 :=
      savitchDepth_windowState_le periodicStrip
    _ ≤ inputLength + 20 * periodicStrip.motif.length + 1 := by
      have periodBound :=
        PeriodicStrip.clog_period_le_encoding_length periodicStrip
      have motifCardBound := periodicStrip.motif.toFinset_card_le
      dsimp only [inputLength] at periodBound ⊢
      omega
    _ ≤ inputLength + 20 * inputLength + 1 := by
      have motifBound :=
        PeriodicStrip.motif_length_le_encoding_length periodicStrip
      dsimp only [inputLength] at motifBound ⊢
      omega
    _ = 21 * inputLength + 1 := by omega

end PeriodicStrip.WindowState
end LeanTrominoes
