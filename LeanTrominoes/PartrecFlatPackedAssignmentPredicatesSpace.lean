import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecFlatPackedAssignmentAtBound
import LeanTrominoes.PartrecFlatPackedAssignmentPredicates

/-!
# Evaluator-space certificates for flat packed-assignment predicates

This module lifts the complete native-field five-column lookup certificate
through digit projection, the `none` test, and comparison with a fixed
assignment state.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedAssignmentLookupDigitCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn
    target word
  getCost 0 [outcome.2.1, outcome.2.2.toNat] +
    flatPackedAssignmentLookupCost motif queriedColumn target word

theorem flatPackedAssignmentLookupDigit
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupDigitCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1]
      (flatPackedAssignmentLookupDigitCost motif queriedColumn target word) := by
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn target
    word
  simpa [Code.flatPackedAssignmentLookupDigitCode,
    flatPackedAssignmentLookupDigitCost, outcome] using
    comp (get 0 [outcome.2.1, outcome.2.2.toNat])
      (flatPackedAssignmentLookup motif queriedColumn target word)

def flatPackedAssignmentIsNoneCost
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  isZeroCost values digit
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)

theorem flatPackedAssignmentIsNone
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentIsNoneCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 then 1 else 0]
      (flatPackedAssignmentIsNoneCost motif queriedColumn target word) := by
  simpa [Code.flatPackedAssignmentIsNoneCode,
    flatPackedAssignmentIsNoneCost] using
    isZero (flatPackedAssignmentLookupDigit motif queriedColumn target word)

def flatPackedAssignmentIsArgumentsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  prependCost values [digit] [RawWindowState.assignmentDigit state]
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)
    (numeralCost (RawWindowState.assignmentDigit state) values)

theorem flatPackedAssignmentIsArguments
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
    EvaluatorCodeFits (Code.flatPackedAssignmentIsArgumentsCode state)
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [digit, RawWindowState.assignmentDigit state]
      (flatPackedAssignmentIsArgumentsCost state motif queriedColumn target
        word) := by
  simp only
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  simpa [Code.flatPackedAssignmentIsArgumentsCode,
    flatPackedAssignmentIsArgumentsCost, prependCost, values] using
    prepend (flatPackedAssignmentLookupDigit motif queriedColumn target word)
      (numeral (RawWindowState.assignmentDigit state) values)

def flatPackedAssignmentIsCost
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
    target word).2.1
  natEqCost digit (RawWindowState.assignmentDigit state) +
    flatPackedAssignmentIsArgumentsCost state motif queriedColumn target word

theorem flatPackedAssignmentIs
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
    EvaluatorCodeFits (Code.flatPackedAssignmentIsCode state)
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if digit = RawWindowState.assignmentDigit state then 1 else 0]
      (flatPackedAssignmentIsCost state motif queriedColumn target word) := by
  simp only
  simpa [Code.flatPackedAssignmentIsCode, flatPackedAssignmentIsCost] using
    comp
      (natEq
        (Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1
        (RawWindowState.assignmentDigit state))
      (flatPackedAssignmentIsArguments state motif queriedColumn target word)

theorem flatPackedAssignmentIs_semantic
    (state : Option SquareSymmetry)
    (periodicStrip : PeriodicStrip) (packed : PackedWindowState)
    (column : WindowColumn) (target : Cell) :
    EvaluatorCodeFits (Code.flatPackedAssignmentIsCode state)
      ([periodicStrip.motif.length, column.val,
          Encodable.encode target.1, Encodable.encode target.2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(decide (packed.assignmentAtCell periodicStrip column target =
        state)).toNat]
      (flatPackedAssignmentIsCost state periodicStrip.motif column.val target
        packed.assignmentWord) := by
  let digit := (Code.packedAssignmentLookupOutcome periodicStrip.motif
    column.val target packed.assignmentWord).2.1
  have digitBound : digit < 9 := by
    simpa [digit] using Code.packedAssignmentLookupOutcome_digit_lt
      periodicStrip.motif column.val target packed.assignmentWord
  have decoded := Code.assignmentOfDigit_packedAssignmentLookupOutcome
    periodicStrip packed column target
  have equivalent :
      digit = RawWindowState.assignmentDigit state ↔
        packed.assignmentAtCell periodicStrip column target = state := by
    rw [← decoded]
    exact (Code.assignmentOfDigit_eq_state_iff digit digitBound state).symm
  have outputEq :
      (if digit = RawWindowState.assignmentDigit state then 1 else 0) =
        (decide (packed.assignmentAtCell periodicStrip column target =
          state)).toNat := by
    by_cases selected :
        packed.assignmentAtCell periodicStrip column target = state
    · rw [if_pos (equivalent.mpr selected)]
      have selectedRaw :
          (packed.toRaw periodicStrip).assignmentAtCell periodicStrip column
            target = state := by simpa using selected
      simp [selectedRaw]
    · rw [if_neg (fun equal => selected (equivalent.mp equal))]
      have selectedRaw : ¬
          (packed.toRaw periodicStrip).assignmentAtCell periodicStrip column
            target = state := by simpa using selected
      simp [selectedRaw]
  have fitted := flatPackedAssignmentIs state periodicStrip.motif column.val
    target packed.assignmentWord
  simpa [digit, outputEq] using fitted

/-! ## Common polynomial bound -/

/-- A generous common budget for the constant-size adapters surrounding the
quadratic five-column lookup. -/
def flatPackedAssignmentPredicateBudget
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  1000000 *
    (flatPackedAssignmentLookupSpaceBound motif queriedColumn target word +
      flatPackedAssignmentLookupNativeInputSpace motif queriedColumn target
        word + 1)

def flatPackedAssignmentPredicateSpaceBound
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) : Nat :=
  1000000 *
    (flatPackedAssignmentPredicateBudget motif queriedColumn target word + 1)

theorem flatPackedAssignmentPredicateBudgetPositive
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    1 ≤ flatPackedAssignmentPredicateBudget motif queriedColumn target word := by
  simp [flatPackedAssignmentPredicateBudget]
  omega

theorem flatPackedAssignmentLookupDigitCost_le_budget
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentLookupDigitCost motif queriedColumn target word ≤
      flatPackedAssignmentPredicateBudget motif queriedColumn target word := by
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn target
    word
  let output := [outcome.2.1, outcome.2.2.toNat]
  let lookupBound := flatPackedAssignmentLookupSpaceBound motif queriedColumn
    target word
  let budget := flatPackedAssignmentPredicateBudget motif queriedColumn target
    word
  have lookupCost := flatPackedAssignmentLookupCost_le_quadratic motif
    queriedColumn target word
  have lookupFit := flatPackedAssignmentLookup motif queriedColumn target word
  have outputSpace : encodedListSpace output ≤ lookupBound := by
    have fittedSpace := lookupFit.output_space
    exact fittedSpace.trans (by simpa [lookupBound] using lookupCost)
  have projectedRaw := listCodeGetCost_le_linear 0 output
  have projected : getCost 0 output ≤ 10000 * (lookupBound + 1) :=
    projectedRaw.trans (by gcongr)
  have budgetForm :
      budget = 1000000 *
        (lookupBound + flatPackedAssignmentLookupNativeInputSpace motif
          queriedColumn target word + 1) := by
    rfl
  change getCost 0 output +
      flatPackedAssignmentLookupCost motif queriedColumn target word ≤ budget
  omega

theorem flatPackedAssignmentIsNoneCost_le_bound
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentIsNoneCost motif queriedColumn target word ≤
      flatPackedAssignmentPredicateSpaceBound motif queriedColumn target
        word := by
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn target
    word
  let digit := outcome.2.1
  let output := [digit, outcome.2.2.toNat]
  let lookupBound := flatPackedAssignmentLookupSpaceBound motif queriedColumn
    target word
  let budget := flatPackedAssignmentPredicateBudget motif queriedColumn target
    word
  have positive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentPredicateBudgetPositive motif
      queriedColumn target word
  have lookupCost := flatPackedAssignmentLookupCost_le_quadratic motif
    queriedColumn target word
  have lookupFit := flatPackedAssignmentLookup motif queriedColumn target word
  have outputSpace : encodedListSpace output ≤ lookupBound := by
    exact lookupFit.output_space.trans (by
      simpa [lookupBound] using lookupCost)
  have digitSpace : encodedListSpace [digit] ≤ budget := by
    have localBound := flatLookupEncodedListSpace_prefix_le [digit]
      [outcome.2.2.toNat]
    have lookupToBudget : lookupBound ≤ budget := by
      simp [budget, flatPackedAssignmentPredicateBudget]
      omega
    exact localBound.trans (outputSpace.trans lookupToBudget)
  have predecessorSpace : encodedListSpace [digit.pred] ≤ budget :=
    (flatLookupSingletonPredSpace_le digit).trans digitSpace
  have nativeForm :
      flatPackedAssignmentLookupNativeInputSpace motif queriedColumn target
        word = encodedListSpace values + 1 := by
    rfl
  have valuesBound : encodedListSpace values ≤ budget := by
    simp [budget, flatPackedAssignmentPredicateBudget, nativeForm]
    omega
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    have localBound :
        (Computability.encodeNat values.headI).length ≤
          encodedListSpace values := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans valuesBound
  have headSuccessor := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    have localBound :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using headSuccessor
    have headPlusSpace :
        (Computability.encodeNat values.headI).length + 1 ≤
          encodedListSpace values := by
      simp [values, encodedListSpace_cons]
    exact localBound.trans (headPlusSpace.trans valuesBound)
  have digitCost := flatPackedAssignmentLookupDigitCost_le_budget motif
    queriedColumn target word
  have wrapped := isZeroCost_le_budget values digit
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)
    budget valuesBound digitSpace predecessorSpace headBound
    headSuccessorBound (by simpa [budget] using digitCost) positive
  change isZeroCost values digit
      (flatPackedAssignmentLookupDigitCost motif queriedColumn target word) ≤
    1000000 * (budget + 1)
  omega

set_option maxHeartbeats 1000000 in
theorem flatPackedAssignmentIsCost_le_bound
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentIsCost state motif queriedColumn target word ≤
      flatPackedAssignmentPredicateSpaceBound motif queriedColumn target
        word := by
  let values :=
    [motif.length, queriedColumn,
        Encodable.encode target.1, Encodable.encode target.2, word] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields
  let outcome := Code.packedAssignmentLookupOutcome motif queriedColumn target
    word
  let digit := outcome.2.1
  let selected := RawWindowState.assignmentDigit state
  let output := [digit, outcome.2.2.toNat]
  let lookupBound := flatPackedAssignmentLookupSpaceBound motif queriedColumn
    target word
  let budget := flatPackedAssignmentPredicateBudget motif queriedColumn target
    word
  have positive : 1 ≤ budget := by
    simpa [budget] using flatPackedAssignmentPredicateBudgetPositive motif
      queriedColumn target word
  have large : 100000000000 ≤ budget := by
    have unitPositive := flatPackedAssignmentUnitPositive motif queriedColumn
      target word
    simp [budget, flatPackedAssignmentPredicateBudget,
      flatPackedAssignmentLookupSpaceBound,
      flatPackedAssignmentScannerBudget]
    nlinarith
  have lookupCost := flatPackedAssignmentLookupCost_le_quadratic motif
    queriedColumn target word
  have lookupFit := flatPackedAssignmentLookup motif queriedColumn target word
  have outputSpace : encodedListSpace output ≤ lookupBound := by
    exact lookupFit.output_space.trans (by
      simpa [lookupBound] using lookupCost)
  have lookupToBudget : lookupBound ≤ budget := by
    simp [budget, flatPackedAssignmentPredicateBudget]
    omega
  have digitSpace : encodedListSpace [digit] ≤ budget :=
    (flatLookupEncodedListSpace_prefix_le [digit]
      [outcome.2.2.toNat]).trans (outputSpace.trans lookupToBudget)
  have nativeForm :
      flatPackedAssignmentLookupNativeInputSpace motif queriedColumn target
        word = encodedListSpace values + 1 := by
    rfl
  have valuesBound : encodedListSpace values ≤ budget := by
    simp [budget, flatPackedAssignmentPredicateBudget, nativeForm]
    omega
  have digitCost := flatPackedAssignmentLookupDigitCost_le_budget motif
    queriedColumn target word
  have digitCostBound :
      flatPackedAssignmentLookupDigitCost motif queriedColumn target word ≤
        budget := by simpa [budget] using digitCost
  have selectedSmall : selected < 9 := by
    simpa [selected] using RawWindowState.assignmentDigit_lt state
  have selectedSpace : encodedListSpace [selected] ≤ budget := by
    have selectedBits := encodeNat_length_mono (show selected ≤ 8 by omega)
    have eightBits : (Computability.encodeNat 8).length = 4 := rfl
    rw [eightBits] at selectedBits
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have pairSpace : encodedListSpace [digit, selected] ≤ budget := by
    have digitToLookup : encodedListSpace [digit] ≤ lookupBound :=
      (flatLookupEncodedListSpace_prefix_le [digit]
        [outcome.2.2.toNat]).trans outputSpace
    have selectedConstant : encodedListSpace [selected] ≤ 5 := by
      have selectedBits := encodeNat_length_mono (show selected ≤ 8 by omega)
      have eightBits : (Computability.encodeNat 8).length = 4 := rfl
      rw [eightBits] at selectedBits
      simp only [encodedListSpace_cons, encodedListSpace_nil]
      omega
    calc
      encodedListSpace [digit, selected] =
          encodedListSpace [digit] + encodedListSpace [selected] := by
        simp [encodedListSpace_cons]
      _ ≤ lookupBound + 5 := Nat.add_le_add digitToLookup selectedConstant
      _ ≤ budget := by
        simp [budget, flatPackedAssignmentPredicateBudget]
        omega
  have zeroRaw := listCodeZeroCost_le_linear values
  have zeroBound : zeroCost values ≤ budget :=
    zeroRaw.trans (by
      simp [budget, flatPackedAssignmentPredicateBudget, nativeForm]
      omega)
  have addSmall : addConstCost selected [0] ≤ 1000000 := by
    cases state with
    | none => native_decide
    | some symmetry => fin_cases symmetry <;> native_decide
  have numeralBound : numeralCost selected values ≤ 2 * budget := by
    simp only [numeralCost]
    omega
  have argumentsEstimate := listCodePrependCost_le_of values [digit]
    [selected]
    (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)
    (numeralCost selected values) budget valuesBound digitSpace pairSpace
  have argumentsBound :
      flatPackedAssignmentIsArgumentsCost state motif queriedColumn target
          word ≤ 7 * budget := by
    change prependCost values [digit] [selected]
        (flatPackedAssignmentLookupDigitCost motif queriedColumn target word)
        (numeralCost selected values) ≤ 7 * budget
    omega
  have digitSmall : digit < 9 := by
    simpa [digit, outcome] using Code.packedAssignmentLookupOutcome_digit_lt
      motif queriedColumn target word
  have equalityRaw := natEqCost_le_linear digit selected
  have equalityArgument : 2 * (digit + selected) + 4 ≤ 36 := by omega
  have equalityBits := encodeNat_length_mono equalityArgument
  have thirtySixBits : (Computability.encodeNat 36).length = 6 := by
    native_decide
  rw [thirtySixBits] at equalityBits
  have equalityBound : natEqCost digit selected ≤ budget :=
    equalityRaw.trans (by
      simp only [encodedListSpace_cons, encodedListSpace_nil]
      omega)
  change natEqCost digit selected +
      flatPackedAssignmentIsArgumentsCost state motif queriedColumn target
        word ≤ 1000000 * (budget + 1)
  omega

/-- The common predicate allowance remains quadratic in the actual native
query footprint. -/
theorem flatPackedAssignmentPredicateSpaceBound_le_native_quadratic
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    flatPackedAssignmentPredicateSpaceBound motif queriedColumn target word ≤
      10000000000000000000000000000000000000000000000000000000000 *
        (flatPackedAssignmentLookupNativeInputSpace motif queriedColumn
          target word) ^ 2 := by
  let native := flatPackedAssignmentLookupNativeInputSpace motif
    queriedColumn target word
  let lookupBound := flatPackedAssignmentLookupSpaceBound motif queriedColumn
    target word
  have nativePositive : 1 ≤ native := by
    simp [native, flatPackedAssignmentLookupNativeInputSpace]
  have lookup := flatPackedAssignmentLookupSpaceBound_le_native_quadratic
    motif queriedColumn target word
  have lookupLocal : lookupBound ≤
      100000000000000000000000000000000000000000000 * native ^ 2 := by
    simpa [lookupBound, native] using lookup
  have nativeLinear : native ≤ native ^ 2 := by nlinarith
  have oneQuadratic : 1 ≤ native ^ 2 := by nlinarith
  change 1000000 * (1000000 * (lookupBound + native + 1) + 1) ≤
    10000000000000000000000000000000000000000000000000000000000 *
      native ^ 2
  nlinarith

theorem flatPackedAssignmentLookupDigitBounded
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentLookupDigitCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [(Code.packedAssignmentLookupOutcome motif queriedColumn target word).2.1]
      (flatPackedAssignmentPredicateSpaceBound motif queriedColumn target
        word) :=
  (flatPackedAssignmentLookupDigit motif queriedColumn target word).mono
    ((flatPackedAssignmentLookupDigitCost_le_budget motif queriedColumn target
      word).trans (by
        simp [flatPackedAssignmentPredicateSpaceBound]
        omega))

theorem flatPackedAssignmentIsNoneBounded
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    EvaluatorCodeFits Code.flatPackedAssignmentIsNoneCode
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if (Code.packedAssignmentLookupOutcome motif queriedColumn
        target word).2.1 = 0 then 1 else 0]
      (flatPackedAssignmentPredicateSpaceBound motif queriedColumn target
        word) :=
  (flatPackedAssignmentIsNone motif queriedColumn target word).mono
    (flatPackedAssignmentIsNoneCost_le_bound motif queriedColumn target word)

theorem flatPackedAssignmentIsBounded
    (state : Option SquareSymmetry)
    (motif : List Cell) (queriedColumn : Nat)
    (target : Cell) (word : Nat) :
    let digit := (Code.packedAssignmentLookupOutcome motif queriedColumn
      target word).2.1
    EvaluatorCodeFits (Code.flatPackedAssignmentIsCode state)
      ([motif.length, queriedColumn,
          Encodable.encode target.1, Encodable.encode target.2, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields)
      [if digit = RawWindowState.assignmentDigit state then 1 else 0]
      (flatPackedAssignmentPredicateSpaceBound motif queriedColumn target
        word) := by
  simp only
  exact (flatPackedAssignmentIs state motif queriedColumn target word).mono
    (flatPackedAssignmentIsCost_le_bound state motif queriedColumn target word)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
