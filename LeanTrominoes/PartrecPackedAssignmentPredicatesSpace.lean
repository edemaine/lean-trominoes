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
open LeanTrominoes.PeriodicStrip

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

def packedAssignmentIsArgumentsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  let digit :=
    (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
  prependCost values [digit] [RawWindowState.assignmentDigit state]
    (packedAssignmentLookupDigitCost
      motif queriedColumn target word)
    (numeralCost (RawWindowState.assignmentDigit state) values)

theorem packedAssignmentIsArguments
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit :=
      (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1
    EvaluatorCodeFits
      (Code.packedAssignmentIsArgumentsCode state)
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [digit, RawWindowState.assignmentDigit state]
      (packedAssignmentIsArgumentsCost
        state motif queriedColumn target word) := by
  simp only
  let values :=
    [Encodable.encode motif, queriedColumn,
      Encodable.encode target, word]
  simpa [Code.packedAssignmentIsArgumentsCode,
    packedAssignmentIsArgumentsCost, prependCost,
    values] using
    prepend
      (packedAssignmentLookupDigit
        motif queriedColumn target word)
      (numeral (RawWindowState.assignmentDigit state) values)

def packedAssignmentIsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let digit :=
    (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
  natEqCost digit (RawWindowState.assignmentDigit state) +
    packedAssignmentIsArgumentsCost
      state motif queriedColumn target word

theorem packedAssignmentIs
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit :=
      (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1
    EvaluatorCodeFits (Code.packedAssignmentIsCode state)
      [Encodable.encode motif, queriedColumn,
        Encodable.encode target, word]
      [if digit = RawWindowState.assignmentDigit state
        then 1 else 0]
      (packedAssignmentIsCost
        state motif queriedColumn target word) := by
  simp only
  simpa [Code.packedAssignmentIsCode,
    packedAssignmentIsCost] using
    comp
      (natEq
        (Code.packedAssignmentLookupOutcome motif queriedColumn
          target word).2.1
        (RawWindowState.assignmentDigit state))
      (packedAssignmentIsArguments
        state motif queriedColumn target word)

theorem packedAssignmentIs_semantic
    (state : Option SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    EvaluatorCodeFits (Code.packedAssignmentIsCode state)
      [Encodable.encode periodicStrip.motif, column.val,
        Encodable.encode target, packed.assignmentWord]
      [(decide
        (packed.assignmentAtCell periodicStrip column target =
          state)).toNat]
      (packedAssignmentIsCost state periodicStrip.motif
        column.val target packed.assignmentWord) := by
  let digit :=
    (Code.packedAssignmentLookupOutcome periodicStrip.motif
      column.val target packed.assignmentWord).2.1
  have digitBound : digit < 9 := by
    simpa [digit] using
      Code.packedAssignmentLookupOutcome_digit_lt
        periodicStrip.motif column.val target packed.assignmentWord
  have decoded :=
    Code.assignmentOfDigit_packedAssignmentLookupOutcome
      periodicStrip packed column target
  have equivalent :
      digit = RawWindowState.assignmentDigit state ↔
        packed.assignmentAtCell periodicStrip column target = state := by
    rw [← decoded]
    exact (Code.assignmentOfDigit_eq_state_iff
      digit digitBound state).symm
  have outputEq :
      (if digit = RawWindowState.assignmentDigit state then 1 else 0) =
        (decide
          (packed.assignmentAtCell periodicStrip column target =
            state)).toNat := by
    by_cases selected :
        packed.assignmentAtCell periodicStrip column target = state
    · rw [if_pos (equivalent.mpr selected)]
      have selectedRaw :
          (packed.toRaw periodicStrip).assignmentAtCell
              periodicStrip column target = state := by
        simpa using selected
      simp [selectedRaw]
    · rw [if_neg (fun equal => selected (equivalent.mp equal))]
      have selectedRaw : ¬
          (packed.toRaw periodicStrip).assignmentAtCell
              periodicStrip column target = state := by
        simpa using selected
      simp [selectedRaw]
  have fitted := packedAssignmentIs state periodicStrip.motif
    column.val target packed.assignmentWord
  simpa [digit, outputEq] using fitted

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

/-- A common polynomial envelope for testing a packed assignment digit
against any fixed frontier state. -/
def packedAssignmentIsSpaceBound
    (motifCode queriedColumn targetCode word : Nat) : Nat :=
  1000000000000000000000000000000000000 *
    (encodedListSpace
      [32 * (motifCode + motifCode + motifCode +
        targetCode + queriedColumn + word + 40 + 32) + 200] + 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem packedAssignmentIsCost_le_linear
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    packedAssignmentIsCost state motif queriedColumn target word ≤
      packedAssignmentIsSpaceBound
        (Encodable.encode motif) queriedColumn
        (Encodable.encode target) word := by
  let motifCode := Encodable.encode motif
  let targetCode := Encodable.encode target
  let outcome :=
    Code.packedAssignmentLookupOutcome motif queriedColumn target word
  let digit := outcome.2.1
  let selected := RawWindowState.assignmentDigit state
  let values := [motifCode, queriedColumn, targetCode, word]
  let limit :=
    32 * (motifCode + motifCode + motifCode +
      targetCode + queriedColumn + word + 40 + 32) + 200
  let unit := encodedListSpace [limit] + 1
  change packedAssignmentIsCost state motif queriedColumn target word ≤
    1000000000000000000000000000000000000 * unit
  have unitPositive : 1 ≤ unit := by simp [unit]
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
  have digitSmall : digit ≤ 40 := by
    simpa [digit, outcome] using
      Code.packedAssignmentLookupOutcome_digit_le
        motif queriedColumn target word
  have digitBound : digit ≤ limit := by
    simp only [limit]
    omega
  have selectedSmall : selected < 9 := by
    simpa [selected] using RawWindowState.assignmentDigit_lt state
  have selectedBound : selected ≤ limit := by
    simp only [limit]
    omega
  have inputSpace : encodedListSpace values ≤ 5 * unit := by
    have raw := encodedListSpace_le_of_fields_le values limit (by
      intro value member
      simp only [values, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | rfl | impossible
      · exact motifBound
      · exact queryBound
      · exact targetBound
      · exact wordBound
      · simp at impossible)
    simp only [values, List.length_cons, List.length_nil] at raw
    change encodedListSpace
      [motifCode, queriedColumn, targetCode, word] ≤ 5 * unit
    simp only [unit, encodedListSpace_cons,
      encodedListSpace_nil] at raw ⊢
    omega
  have digitBits := listCodeEncodeNat_length_mono digitBound
  have selectedBits := listCodeEncodeNat_length_mono selectedBound
  have digitCost := packedAssignmentLookupDigitCost_le_linear
    motif queriedColumn target word
  have digitCostBound :
      packedAssignmentLookupDigitCost motif queriedColumn target word ≤
        800000000000000000000 * unit := by
    simpa [packedAssignmentLookupDigitSpaceBound,
      motifCode, targetCode, limit, unit] using digitCost
  have equalityLimit : 2 * (digit + selected) + 4 ≤ limit := by
    simp only [limit]
    omega
  have equalityBits := listCodeEncodeNat_length_mono equalityLimit
  have equalityCost := natEqCost_le_linear digit selected
  have equalityCostBound :
      natEqCost digit selected ≤ 10000000000 * unit := by
    exact equalityCost.trans (by
      simp only [unit, encodedListSpace_cons,
        encodedListSpace_nil] at equalityBits ⊢
      omega)
  have zeroCostBound := listCodeZeroCost_le_linear values
  have addCostSmall : addConstCost selected [0] ≤ 1000000 := by
    cases state with
    | none => native_decide
    | some symmetry => fin_cases symmetry <;> native_decide
  have numeralCostBound :
      numeralCost selected values ≤ 100000000 * unit := by
    simp only [numeralCost]
    omega
  have argumentsCostBound :
      packedAssignmentIsArgumentsCost state motif queriedColumn
          target word ≤
        1000000000000000000000000 * unit := by
    change
      prependCost values [digit] [selected]
          (packedAssignmentLookupDigitCost
            motif queriedColumn target word)
          (numeralCost selected values) ≤
        1000000000000000000000000 * unit
    simp only [prependCost]
    simp only [unit, encodedListSpace_cons,
      encodedListSpace_nil, List.headI_cons] at *
    omega
  change
    natEqCost digit selected +
        packedAssignmentIsArgumentsCost state motif queriedColumn
          target word ≤
      1000000000000000000000000000000000000 * unit
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
