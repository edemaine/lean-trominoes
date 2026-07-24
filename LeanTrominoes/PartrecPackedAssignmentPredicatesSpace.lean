import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecPackedAssignmentAtSpace
import LeanTrominoes.PartrecPackedAssignmentPredicates

/-!
# Evaluator-space certificates for packed assignment predicates

The packed `none` predicate first projects the digit returned by the complete
five-column lookup and then performs one fitted zero test.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def packedAssignmentLookupDigitCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  getCost 0 [outcome.2.1, outcome.2.2.toNat] +
    packedAssignmentLookupCodeCost motif queriedColumn target word

theorem packedAssignmentLookupDigit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentLookupDigitCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [(Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1]
      (packedAssignmentLookupDigitCost motif queriedColumn
        target word) := by
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  simpa [Code.packedAssignmentLookupDigitCode,
    packedAssignmentLookupDigitCost, outcome] using
    comp
      (get 0 [outcome.2.1, outcome.2.2.toNat])
      (packedAssignmentLookup motif queriedColumn target word)

def packedAssignmentIsNoneCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  let digit :=
    (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
  isZeroCost values digit
    (packedAssignmentLookupDigitCost motif queriedColumn target word)

theorem packedAssignmentIsNone
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedAssignmentIsNoneCode
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [if (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 then 1 else 0]
      (packedAssignmentIsNoneCost motif queriedColumn target word) := by
  simpa [Code.packedAssignmentIsNoneCode,
    packedAssignmentIsNoneCost] using
    isZero
      (packedAssignmentLookupDigit motif queriedColumn target word)

def packedAssignmentLookupDigitSpaceBound
    (motifCode queriedColumn targetCode word : Nat) : Nat :=
  800000000000000000000 *
    (encodedListSpace
      [32 * (motifCode + motifCode + motifCode +
        targetCode + queriedColumn + word + 40 + 32) + 200] + 1)

set_option maxHeartbeats 800000 in
theorem packedAssignmentLookupDigitCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentLookupDigitCost motif queriedColumn target word ≤
      packedAssignmentLookupDigitSpaceBound
        (Encodable.encode motif) queriedColumn
        (Encodable.encode target) word := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  let digit := outcome.2.1
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + word + 40 + 32) + 200
  change
    packedAssignmentLookupDigitCost motif queriedColumn target word ≤
      800000000000000000000 *
        (encodedListSpace [limit] + 1)
  have digitBound : digit ≤ 40 := by
    simpa [digit, outcome] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif queriedColumn target word
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have queryBound : queriedColumn ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have digitLimit : digit ≤ limit := by
    simp only [limit]
    omega
  have motifBits := encodeNat_length_mono motifBound
  have targetBits := encodeNat_length_mono targetBound
  have queryBits := encodeNat_length_mono queryBound
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitLimit
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have querySuccBits :=
    encodeNat_length_mono
      (show queriedColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show word + 1 ≤ limit by
        simp only [limit]
        omega)
  have digitSuccBits :=
    encodeNat_length_mono
      (show digit + 1 ≤ limit by
        simp only [limit]
        omega)
  have lookup :=
    packedAssignmentLookupCodeCost_le_linear
      motif queriedColumn target word
  have lookupGlobal :
      packedAssignmentLookupCodeCost motif queriedColumn target word ≤
        700000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [packedAssignmentLookupSpaceBound,
      limit, motifCode, targetCode] using lookup
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  cases found : outcome.2.2 <;>
    simp [packedAssignmentLookupDigitCost,
      getCost, dropCost, headCost, idCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      outcome, digit, found, zeroBits, oneBits] at * <;>
    omega

def packedAssignmentIsNoneSpaceBound
    (motifCode queriedColumn targetCode word : Nat) : Nat :=
  1000000000000000000000000 *
    (encodedListSpace
      [32 * (motifCode + motifCode + motifCode +
        targetCode + queriedColumn + word + 40 + 32) + 200] + 1)

set_option maxHeartbeats 800000 in
theorem packedAssignmentIsNoneCost_le_linear
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentIsNoneCost motif queriedColumn target word ≤
      packedAssignmentIsNoneSpaceBound
        (Encodable.encode motif) queriedColumn
        (Encodable.encode target) word := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  let digit := outcome.2.1
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + word + 40 + 32) + 200
  change
    packedAssignmentIsNoneCost motif queriedColumn target word ≤
      1000000000000000000000000 *
        (encodedListSpace [limit] + 1)
  have digitBound : digit ≤ 40 := by
    simpa [digit, outcome] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif queriedColumn target word
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have targetBound : targetCode ≤ limit := by
    simp only [limit]
    omega
  have queryBound : queriedColumn ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have digitLimit : digit ≤ limit := by
    simp only [limit]
    omega
  have digitPredLimit : digit.pred ≤ limit :=
    (Nat.pred_le digit).trans digitLimit
  have motifBits := encodeNat_length_mono motifBound
  have targetBits := encodeNat_length_mono targetBound
  have queryBits := encodeNat_length_mono queryBound
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitLimit
  have digitPredBits :=
    encodeNat_length_mono digitPredLimit
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have targetSuccBits :=
    encodeNat_length_mono
      (show targetCode + 1 ≤ limit by
        simp only [limit]
        omega)
  have querySuccBits :=
    encodeNat_length_mono
      (show queriedColumn + 1 ≤ limit by
        simp only [limit]
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show word + 1 ≤ limit by
        simp only [limit]
        omega)
  have digitSuccBits :=
    encodeNat_length_mono
      (show digit + 1 ≤ limit by
        simp only [limit]
        omega)
  have lookup :=
    packedAssignmentLookupCodeCost_le_linear
      motif queriedColumn target word
  have lookupGlobal :
      packedAssignmentLookupCodeCost motif queriedColumn target word ≤
        700000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    simpa [packedAssignmentLookupSpaceBound,
      limit, motifCode, targetCode] using lookup
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have digitCost :
      packedAssignmentLookupDigitCost motif queriedColumn target word ≤
        800000000000000000000 *
          (encodedListSpace [limit] + 1) := by
    cases found : outcome.2.2 <;>
      simp [packedAssignmentLookupDigitCost,
        getCost, dropCost, headCost, idCost, nilCost,
        tailCost, zeroPrimeCost, succCost,
        encodedListSpace_cons, encodedListSpace_nil,
        outcome, digit, found, zeroBits, oneBits] at * <;>
      omega
  by_cases digitZero : digit = 0
  · simp [packedAssignmentIsNoneCost, isZeroCost,
      branchZeroZeroCost, branchZeroTestCost,
      prependCost, idCost, nilCost,
      zeroCost, oneCost, zeroPrimeCost, tailCost,
      succCost, encodedListSpace_cons,
      encodedListSpace_nil, motifCode, targetCode,
      outcome, digit, digitZero, zeroBits, oneBits] at *
    omega
  · simp [packedAssignmentIsNoneCost, isZeroCost,
      branchZeroSuccCost, branchZeroTestCost,
      prependCost, idCost, nilCost,
      zeroCost, zeroPrimeCost, tailCost,
      succCost, encodedListSpace_cons,
      encodedListSpace_nil, motifCode, targetCode,
      outcome, digit, digitZero, zeroBits, oneBits] at *
    omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
