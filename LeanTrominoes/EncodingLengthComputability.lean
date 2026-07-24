import LeanTrominoes.Complexity
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursive binary encoding length

The PSPACE strip evaluator needs the actual bit length of a standard
`Primcodable` input, not its (exponentially larger) natural-number code.  The
routine below repeatedly halves the code while incrementing a counter.  It
uses a number of iterations bounded by the code but retains only the current
quotient and counter.
-/

open Computability

namespace LeanTrominoes.Computability

private theorem encodeNat_pos (number : PosNum) :
    encodeNat (number : Nat) = encodePosNum number := by
  change encodeNum ((number : Nat) : Num) = encodePosNum number
  rw [show ((number : Nat) : Num) = Num.pos number from
    PosNum.of_to_nat number]
  rfl

theorem encodeNat_cons (number : Nat) (positive : 0 < number) :
    encodeNat number =
      number.bodd :: encodeNat number.div2 := by
  rw [← Num.to_of_nat number] at positive ⊢
  generalize (number : Num) = encoded at positive ⊢
  cases encoded with
  | zero => simp at positive
  | pos encoded =>
      cases encoded with
      | one =>
          change encodeNat (PosNum.one : Nat) =
            (PosNum.one : Nat).bodd ::
              encodeNat (PosNum.one : Nat).div2
          rw [encodeNat_pos]
          rfl
      | bit1 encoded =>
          change encodeNat (encoded.bit1 : Nat) =
            (encoded.bit1 : Nat).bodd ::
              encodeNat (encoded.bit1 : Nat).div2
          rw [encodeNat_pos, encodePosNum]
          rw [show (encoded.bit1 : Nat) =
            Nat.bit true (encoded : Nat) by
              simp [PosNum.cast_bit1, Nat.bit_val, two_mul]]
          rw [Nat.bodd_bit, Nat.div2_bit, encodeNat_pos]
      | bit0 encoded =>
          change encodeNat (encoded.bit0 : Nat) =
            (encoded.bit0 : Nat).bodd ::
              encodeNat (encoded.bit0 : Nat).div2
          rw [encodeNat_pos, encodePosNum]
          rw [show (encoded.bit0 : Nat) =
            Nat.bit false (encoded : Nat) by
              simp [PosNum.cast_bit0, Nat.bit_val, two_mul]]
          rw [Nat.bodd_bit, Nat.div2_bit, encodeNat_pos]

/-- One bounded-loop step: discard the least significant bit and increment
the length, or remain at zero once all bits have been consumed. -/
def binaryEncodingLengthStep (state : Nat × Nat) : Nat × Nat :=
  if state.1 = 0 then state else (state.1.div2, state.2 + 1)

/-- Length of Mathlib's little-endian binary natural encoding, computed by a
bounded loop that stores only a quotient and a counter. -/
def binaryEncodingLength (number : Nat) : Nat :=
  ((binaryEncodingLengthStep^[number]) (number, 0)).2

theorem binaryEncodingLengthStep_primrec :
    Primrec binaryEncodingLengthStep := by
  unfold binaryEncodingLengthStep
  exact Primrec.ite
    (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    Primrec.id
    (Primrec.pair
      (Primrec.nat_div2.comp Primrec.fst)
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))

theorem binaryEncodingLength_primrec :
    Primrec binaryEncodingLength := by
  have iterated : Primrec fun number =>
      (binaryEncodingLengthStep^[number]) (number, 0) :=
    Primrec.nat_iterate Primrec.id
      (Primrec.pair Primrec.id (Primrec.const 0))
      (binaryEncodingLengthStep_primrec.comp₂ Primrec₂.right)
  exact Primrec.snd.comp iterated

theorem binaryEncodingLengthStep_preserves (state : Nat × Nat) :
    (binaryEncodingLengthStep state).2 +
        (encodeNat (binaryEncodingLengthStep state).1).length =
      state.2 + (encodeNat state.1).length := by
  by_cases zero : state.1 = 0
  · simp [binaryEncodingLengthStep, zero]
  · have positive : 0 < state.1 := Nat.pos_of_ne_zero zero
    rw [binaryEncodingLengthStep, if_neg zero,
      encodeNat_cons state.1 positive]
    simp
    omega

theorem binaryEncodingLengthIterate_preserves
    (steps : Nat) (state : Nat × Nat) :
    ((binaryEncodingLengthStep^[steps]) state).2 +
        (encodeNat
          ((binaryEncodingLengthStep^[steps]) state).1).length =
      state.2 + (encodeNat state.1).length := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      exact (binaryEncodingLengthStep_preserves
        ((binaryEncodingLengthStep^[steps]) state)).trans
          (induction state)

theorem binaryEncodingLengthIterate_fst_zero
    (fuel remaining count : Nat) (bounded : remaining ≤ fuel) :
    ((binaryEncodingLengthStep^[fuel]) (remaining, count)).1 = 0 := by
  induction fuel generalizing remaining count with
  | zero =>
      have : remaining = 0 := by omega
      subst remaining
      rfl
  | succ fuel induction =>
      rw [Function.iterate_succ_apply]
      by_cases zero : remaining = 0
      · simp [binaryEncodingLengthStep, zero, induction]
      · simp only [binaryEncodingLengthStep, zero, ↓reduceIte]
        apply induction
        have smaller : remaining.div2 < remaining := by
          rw [Nat.div2_val]
          exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by omega)
        omega

@[simp]
theorem binaryEncodingLength_eq (number : Nat) :
    binaryEncodingLength number = (encodeNat number).length := by
  have invariant :=
    binaryEncodingLengthIterate_preserves number (number, 0)
  have finished :=
    binaryEncodingLengthIterate_fst_zero number number 0 (by rfl)
  unfold binaryEncodingLength
  rw [finished] at invariant
  simpa [encodeNat, encodeNum] using invariant

theorem primcodableFinEncodingLength_primrec
    (α : Type*) [Primcodable α] :
    Primrec fun input : α =>
      ((Complexity.primcodableFinEncoding α).encode input).length := by
  have computed : Primrec fun input : α =>
      binaryEncodingLength (Encodable.encode input) + 1 :=
    Primrec.nat_add.comp
      (binaryEncodingLength_primrec.comp Primrec.encode)
      (Primrec.const 1)
  exact computed.of_eq fun input => by
    rw [Complexity.primcodableFinEncoding_encode_length,
      binaryEncodingLength_eq]

end LeanTrominoes.Computability
