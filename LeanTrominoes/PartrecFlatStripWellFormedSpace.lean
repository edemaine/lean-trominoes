import LeanTrominoes.PartrecFlatStripWellFormed
import LeanTrominoes.PartrecPairSpace
import LeanTrominoes.PartrecStripCellBoundsSpace
import LeanTrominoes.PeriodicStripFlatEncodingSize

/-!
# Evaluator-space certificates for flat strip well-formedness

This module fits the individual coordinate-pair step used by the flat motif
scanner.  The exact certificates retain the unconsumed coordinate suffix as a
native list; subsequent uniform bounds can therefore charge that suffix
directly to the original flat input stream.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

theorem encodedFieldSpace_le_of_mem
    (field : Nat) (fields : List Nat) (member : field ∈ fields) :
    (Computability.encodeNat field).length + 1 ≤
      encodedListSpace fields := by
  induction fields with
  | nil => simp at member
  | cons value fields induction =>
      rw [encodedListSpace_cons]
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · omega
      · exact (induction member).trans (by omega)

theorem encodedListSpace_suffix_le
    (leadingFields suffix : List Nat) :
    encodedListSpace suffix ≤
      encodedListSpace (leadingFields ++ suffix) := by
  rw [LeanTrominoes.FiniteState.encodedListSpace_append]
  omega

def flatStripMotifCellPairArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [Encodable.encode cell.1] [Encodable.encode cell.2]
    (getCost 3 state) (getCost 4 state)

theorem flatStripMotifCellPairArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellPairArgumentsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [Encodable.encode cell.1, Encodable.encode cell.2]
      (flatStripMotifCellPairArgumentsCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [Code.flatStripMotifCellPairArgumentsCode,
    flatStripMotifCellPairArgumentsCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 3 state) (get 4 state)

def flatStripMotifCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) +
    flatStripMotifCellPairArgumentsCost width period valid cell remaining

theorem flatStripMotifCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [Encodable.encode cell]
      (flatStripMotifCellCost width period valid cell remaining) := by
  rcases cell with ⟨x, y⟩
  simpa [Code.flatStripMotifCellCode, flatStripMotifCellCost] using
    comp (natPair (Encodable.encode x) (Encodable.encode y))
      (flatStripMotifCellPairArguments width period valid (x, y) remaining)

def flatStripMotifPeriodAndCellCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [period] [Encodable.encode cell]
    (getCost 2 state)
    (flatStripMotifCellCost width period valid cell remaining)

theorem flatStripMotifPeriodAndCell
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) Code.flatStripMotifCellCode)
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [period, Encodable.encode cell]
      (flatStripMotifPeriodAndCellCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifPeriodAndCellCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 2 state)
      (flatStripMotifCell width period valid cell remaining)

def flatStripMotifCellArgumentsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  prependCost state [width] [period, Encodable.encode cell]
    (getCost 1 state)
    (flatStripMotifPeriodAndCellCost width period valid cell remaining)

theorem flatStripMotifCellArguments
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifCellArgumentsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [width, period, Encodable.encode cell]
      (flatStripMotifCellArgumentsCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [Code.flatStripMotifCellArgumentsCode,
    flatStripMotifCellArgumentsCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 1 state)
      (flatStripMotifPeriodAndCell width period valid cell remaining)

def flatStripMotifHeadInBoundsCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  stripCellInBoundsCost width period cell +
    flatStripMotifCellArgumentsCost width period valid cell remaining

theorem flatStripMotifHeadInBounds
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifHeadInBoundsCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [if cell.InStripBounds width period then 1 else 0]
      (flatStripMotifHeadInBoundsCost
        width period valid cell remaining) := by
  simpa [Code.flatStripMotifHeadInBoundsCode,
    flatStripMotifHeadInBoundsCost] using
    comp (stripCellInBounds width period cell)
      (flatStripMotifCellArguments width period valid cell remaining)

def flatStripMotifUpdatedValidCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let cellTag := if cell.InStripBounds width period then 1 else 0
  boolAndCost state valid.toNat cellTag
    (getCost 0 state)
    (flatStripMotifHeadInBoundsCost width period valid cell remaining)

theorem flatStripMotifUpdatedValid
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifUpdatedValidCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      [(valid && decide (cell.InStripBounds width period)).toNat]
      (flatStripMotifUpdatedValidCost
        width period valid cell remaining) := by
  have combined :=
    boolAnd
      (get 0
        (Code.flatStripMotifState width period valid (cell :: remaining)))
      (flatStripMotifHeadInBounds width period valid cell remaining)
  cases valid <;>
    by_cases inBounds : cell.InStripBounds width period <;>
    simpa [Code.flatStripMotifUpdatedValidCode,
      flatStripMotifUpdatedValidCost, Code.flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields, inBounds] using combined

def flatStripMotifPeriodAndRestCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [period] rest
    (getCost 2 state) (dropCost 5 state)

theorem flatStripMotifPeriodAndRest
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 2) (Code.drop 5))
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (period ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripMotifPeriodAndRestCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifPeriodAndRestCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 2 state) (drop 5 state)

def flatStripMotifDimensionsAndRestCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [width] (period :: rest)
    (getCost 1 state)
    (flatStripMotifPeriodAndRestCost width period valid cell remaining)

theorem flatStripMotifDimensionsAndRest
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 1) <|
        Code.prepend (Code.get 2) (Code.drop 5))
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (width :: period ::
        remaining.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripMotifDimensionsAndRestCost
        width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  simpa [flatStripMotifDimensionsAndRestCost, state, prependCost,
    Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields] using
    prepend (get 1 state)
      (flatStripMotifPeriodAndRest width period valid cell remaining)

def flatStripMotifStepCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let nextValid := valid && decide (cell.InStripBounds width period)
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost state [nextValid.toNat] (width :: period :: rest)
    (flatStripMotifUpdatedValidCost width period valid cell remaining)
    (flatStripMotifDimensionsAndRestCost width period valid cell remaining)

theorem flatStripMotifStep
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifStepCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (Code.flatStripMotifState width period
        (valid && decide (cell.InStripBounds width period)) remaining)
      (flatStripMotifStepCost width period valid cell remaining) := by
  have fitted :=
    prepend
      (flatStripMotifUpdatedValid width period valid cell remaining)
      (flatStripMotifDimensionsAndRest width period valid cell remaining)
  simpa [Code.flatStripMotifStepCode, flatStripMotifStepCost,
    Code.flatStripMotifState, PeriodicStripFlatEncoding.cellFields,
    prependCost] using fitted

def flatStripMotifBodyCost
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  flatCountdownBodyCost Code.flatStripMotifNativeStep
    (fun _ => flatStripMotifStepCost width period valid cell remaining)
    remainingCount
    (Code.flatStripMotifState width period valid (cell :: remaining))

theorem flatStripMotifBodySucc
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      ((remainingCount + 1) ::
        Code.flatStripMotifState width period valid (cell :: remaining))
      (flatCountdownOutput Code.flatStripMotifNativeStep
        (remainingCount + 1)
        (Code.flatStripMotifState width period valid (cell :: remaining)))
      (flatStripMotifBodyCost
        (remainingCount + 1) width period valid cell remaining) := by
  let payload :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let values := remainingCount :: payload
  have transformed :=
    comp (flatStripMotifStep width period valid cell remaining)
      (tail_named values)
  have payloadResult := prepend (head values) transformed
  have branch := prepend (one values) payloadResult
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatStripMotifBodyCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, payload, values, prependCost,
    Code.prepend] using
    EvaluatorCodeFits.case_succ
      (zeroBranch := Code.zero')
      (values := (remainingCount + 1) :: payload)
      (predecessor := remainingCount) (by rfl) branch

def flatStripMotifBodyZeroCost
    (width period : Nat) (valid : Bool) : Nat :=
  flatCountdownBodyCost Code.flatStripMotifNativeStep
    (fun _ => 0) 0 (Code.flatStripMotifState width period valid [])

theorem flatStripMotifBodyZero
    (width period : Nat) (valid : Bool) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      (0 :: Code.flatStripMotifState width period valid [])
      (flatCountdownOutput Code.flatStripMotifNativeStep 0
        (Code.flatStripMotifState width period valid []))
      (flatStripMotifBodyZeroCost width period valid) := by
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatStripMotifBodyZeroCost, flatCountdownBodyCost,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            (Code.flatStripMotifStepCode.comp Code.tail)))
      (values :=
        0 :: Code.flatStripMotifState width period valid [])
      (by rfl)
      (zero'_named (Code.flatStripMotifState width period valid []))

set_option maxHeartbeats 1500000 in
/-- One positive scanner body costs at most one fixed multiple of the complete
original flat field stream. -/
theorem flatStripMotifBodyCost_le_input
    (periodicStrip : PeriodicStrip)
    (valid : Bool) (cell : Cell) (remaining leading : List Cell)
    (decomposition :
      periodicStrip.motif = leading ++ cell :: remaining) :
    flatStripMotifBodyCost (remaining.length + 1)
        periodicStrip.width periodicStrip.period valid cell remaining ≤
      1000000000000000000000000000000000000000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputSpace := encodedListSpace fields
  let xCode := Encodable.encode cell.1
  let yCode := Encodable.encode cell.2
  let cellCode := Encodable.encode cell
  let restFields :=
    remaining.flatMap PeriodicStripFlatEncoding.cellFields
  let state :=
    Code.flatStripMotifState periodicStrip.width
      periodicStrip.period valid (cell :: remaining)
  have fieldsEq :
      fields =
        [periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length] ++
        (leading.flatMap PeriodicStripFlatEncoding.cellFields ++
          PeriodicStripFlatEncoding.cellFields cell ++ restFields) := by
    simp [fields, PeriodicStripFlatEncoding.stripFields,
      decomposition, restFields, List.flatMap_append,
      List.append_assoc]
  have widthMember : periodicStrip.width ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have periodMember : periodicStrip.period ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have lengthMember : periodicStrip.motif.length ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have xMember : xCode ∈ fields := by
    rw [fieldsEq]
    simp [xCode, PeriodicStripFlatEncoding.cellFields]
  have yMember : yCode ∈ fields := by
    rw [fieldsEq]
    simp [yCode, PeriodicStripFlatEncoding.cellFields]
  have widthSpace := encodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := encodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have motifLengthSpace := encodedFieldSpace_le_of_mem
    periodicStrip.motif.length fields lengthMember
  have xSpace := encodedFieldSpace_le_of_mem xCode fields xMember
  have ySpace := encodedFieldSpace_le_of_mem yCode fields yMember
  have inputExpanded :
      inputSpace =
        (Computability.encodeNat periodicStrip.width).length + 1 +
        ((Computability.encodeNat periodicStrip.period).length + 1 +
        ((Computability.encodeNat periodicStrip.motif.length).length + 1 +
        (encodedListSpace
          (leading.flatMap PeriodicStripFlatEncoding.cellFields) +
        ((Computability.encodeNat xCode).length + 1 +
        ((Computability.encodeNat yCode).length + 1 +
          encodedListSpace restFields))))) := by
    rw [fieldsEq]
    simp [inputSpace,
      LeanTrominoes.FiniteState.encodedListSpace_append,
      PeriodicStripFlatEncoding.cellFields, xCode, yCode]
  have restSpace : encodedListSpace restFields ≤ inputSpace := by
    have suffix := encodedListSpace_suffix_le
      ([periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length] ++
        leading.flatMap PeriodicStripFlatEncoding.cellFields ++
        PeriodicStripFlatEncoding.cellFields cell)
      restFields
    rw [← fieldsEq]
    simpa [List.append_assoc, inputSpace] using suffix
  have remainingCount :
      remaining.length + 1 ≤ periodicStrip.motif.length := by
    rw [decomposition]
    simp
  have remainingCountBits :=
    listCodeEncodeNat_length_mono remainingCount
  have pairBits := encodeNat_pair_length_le xCode yCode
  have pairCost := natPairCost_le_linear xCode yCode
  have pairUnit := natPairUnit_le_linear xCode yCode
  have pairCostInput :
      natPairCost xCode yCode ≤
        100000000000000000000000000000000000000000000 *
          (inputSpace + 1) := by
    omega
  have cellCodeEq : cellCode = Nat.pair xCode yCode := by
    rcases cell with ⟨x, y⟩
    rfl
  have widthPeriodBits :=
    encodeNat_add_length_le_sum periodicStrip.width periodicStrip.period
  have withCellBits :=
    encodeNat_add_length_le_sum
      (periodicStrip.width + periodicStrip.period) cellCode
  have doubledBits :=
    encodeNat_mul_length_le_sum 2
      (periodicStrip.width + periodicStrip.period + cellCode)
  have localBits :=
    encodeNat_add_length_le_sum
      (2 * (periodicStrip.width + periodicStrip.period + cellCode)) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := rfl
  have fourBits : (Computability.encodeNat 4).length = 3 := rfl
  have cellPredicate :=
    stripCellInBoundsCost_le_linear
      periodicStrip.width periodicStrip.period cell
  have cellPredicateInput :
      stripCellInBoundsCost periodicStrip.width periodicStrip.period cell ≤
        10000000000000 * (inputSpace + 1) := by
    simp only [cellCode] at pairBits withCellBits doubledBits localBits
    simp only [encodedListSpace_cons, encodedListSpace_nil] at cellPredicate
    omega
  have stateSpace : encodedListSpace state ≤ inputSpace + 2 := by
    have rest := restSpace
    cases valid <;>
      simp [state, Code.flatStripMotifState,
        PeriodicStripFlatEncoding.cellFields,
        encodedListSpace_cons, restFields] at inputExpanded ⊢ <;>
      omega
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have remainingBits :=
    listCodeEncodeNat_length_mono
      (show remaining.length ≤ remaining.length + 1 by omega)
  have widthSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.width
  have periodSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.period
  have xSuccBits := listCodeEncodeNat_succ_length_le xCode
  have ySuccBits := listCodeEncodeNat_succ_length_le yCode
  have remainingSuccBits :=
    listCodeEncodeNat_succ_length_le remaining.length
  cases valid <;>
    by_cases inBounds :
      cell.InStripBounds periodicStrip.width periodicStrip.period <;>
  simp [flatStripMotifBodyCost, flatCountdownBodyCost,
    flatCountdownSuccBranchCost, flatStripMotifStepCost,
    flatStripMotifUpdatedValidCost,
    flatStripMotifHeadInBoundsCost,
    flatStripMotifCellArgumentsCost,
    flatStripMotifPeriodAndCellCost, flatStripMotifCellCost,
    flatStripMotifCellPairArgumentsCost,
    flatStripMotifDimensionsAndRestCost,
    flatStripMotifPeriodAndRestCost,
    prependCost, boolAndCost, normalizeBoolCost,
    branchZeroZeroCost, branchZeroSuccCost, branchZeroTestCost,
    getCost, dropCost, idCost, headCost, nilCost, oneCost,
    zeroCost, zeroPrimeCost, tailCost, succCost,
    Code.flatStripMotifNativeStep, Code.flatStripMotifState,
    PeriodicStripFlatEncoding.cellFields,
    encodedListSpace_cons, encodedListSpace_nil,
    fields, inputSpace, xCode, yCode, cellCode, cellCodeEq,
    restFields, state, zeroBits, oneBits] at *
  all_goals omega

theorem flatStripMotifBodyZeroCost_le_input
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    flatStripMotifBodyZeroCost periodicStrip.width periodicStrip.period valid ≤
      1000000000000000000000000000000000000000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputSpace := encodedListSpace fields
  have widthMember : periodicStrip.width ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have periodMember : periodicStrip.period ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have widthSpace := encodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := encodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases valid <;>
    simp [flatStripMotifBodyZeroCost, flatCountdownBodyCost,
      zeroPrimeCost, Code.flatStripMotifState,
      encodedListSpace_cons, encodedListSpace_nil,
      fields, inputSpace, zeroBits, oneBits] at * <;>
    omega

/-- Exact (deliberately additive) cost of scanning a typed flat motif.  This
cost is later bounded quadratically in the original flat input length. -/
def flatStripMotifFlatCost
    (width period : Nat) : Bool → List Cell → Nat
  | valid, [] => flatStripMotifBodyZeroCost width period valid
  | valid, cell :: remaining =>
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      flatStripMotifBodyCost (remaining.length + 1)
          width period valid cell remaining +
        flatStripMotifFlatCost width period nextValid remaining

theorem flatStripMotifFlatCost_le_input_mul
    (periodicStrip : PeriodicStrip) (valid : Bool)
    (motif leading : List Cell)
    (decomposition : periodicStrip.motif = leading ++ motif) :
    flatStripMotifFlatCost periodicStrip.width periodicStrip.period
        valid motif ≤
      1000000000000000000000000000000000000000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) *
        (motif.length + 1) := by
  induction motif generalizing valid leading with
  | nil =>
      simpa [flatStripMotifFlatCost] using
        flatStripMotifBodyZeroCost_le_input periodicStrip valid
  | cons cell remaining induction =>
      let unit :=
        1000000000000000000000000000000000000000000000 *
          (encodedListSpace
            (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1)
      have body :=
        flatStripMotifBodyCost_le_input periodicStrip valid cell remaining
          leading decomposition
      have tailDecomposition :
          periodicStrip.motif = (leading ++ [cell]) ++ remaining := by
        simpa [List.append_assoc] using decomposition
      let nextValid :=
        valid && decide (cell.InStripBounds periodicStrip.width
          periodicStrip.period)
      have tail := induction nextValid (leading ++ [cell]) tailDecomposition
      simp only [flatStripMotifFlatCost, List.length_cons]
      simp only [unit] at body tail ⊢
      nlinarith

/-- The complete typed motif countdown has a quadratic bound in the target
flat input length. -/
theorem flatStripMotifFlatCost_le_quadratic
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    flatStripMotifFlatCost periodicStrip.width periodicStrip.period
        valid periodicStrip.motif ≤
      1000000000000000000000000000000000000000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) ^ 2 := by
  let inputSpace :=
    encodedListSpace (PeriodicStripFlatEncoding.stripFields periodicStrip)
  have additive :=
    flatStripMotifFlatCost_le_input_mul periodicStrip valid
      periodicStrip.motif [] (by simp)
  have encodingLength :
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length =
        inputSpace := by
    rw [PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
    rfl
  have motifLength :=
    PeriodicStripFlatEncoding.motif_length_le_encoding_length periodicStrip
  rw [encodingLength] at motifLength
  simp only [inputSpace] at additive ⊢
  have factor : periodicStrip.motif.length + 1 ≤ inputSpace + 1 := by
    omega
  calc
    _ ≤ 1000000000000000000000000000000000000000000000 *
          (inputSpace + 1) * (periodicStrip.motif.length + 1) :=
      additive
    _ ≤ 1000000000000000000000000000000000000000000000 *
          (inputSpace + 1) * (inputSpace + 1) := by
      exact Nat.mul_le_mul_left _ factor
    _ = _ := by ring

theorem flatStripMotifResultSpace_le_flatCost
    (width period : Nat) (valid : Bool) (motif : List Cell) :
    encodedListSpace
        (Code.flatStripMotifState width period
          (valid && motifInStripBounds width period motif) []) ≤
      flatStripMotifFlatCost width period valid motif := by
  induction motif generalizing valid with
  | nil =>
      have output :=
        (flatStripMotifBodyZero width period valid).output_space
      simp [flatCountdownOutput, flatStripMotifFlatCost,
        Code.flatStripMotifState] at output ⊢
      omega
  | cons cell remaining induction =>
      let nextValid :=
        valid && decide (cell.InStripBounds width period)
      have result := induction nextValid
      simpa [flatStripMotifFlatCost, nextValid, Bool.and_assoc] using
        result.trans (Nat.le_add_left _ _)

theorem flatStripMotifFlat
    (width period : Nat) (valid : Bool) (motif : List Cell) :
    EvaluatorCodeFits
      (Code.flatIterate Code.flatStripMotifStepCode)
      (motif.length ::
        Code.flatStripMotifState width period valid motif)
      (Code.flatStripMotifState width period
        (valid && motifInStripBounds width period motif) [])
      (flatStripMotifFlatCost width period valid motif) where
  input_space := by
    cases motif with
    | nil =>
        exact (flatStripMotifBodyZero width period valid).input_space
    | cons cell remaining =>
        exact
          (flatStripMotifBodySucc remaining.length width period valid
            cell remaining).input_space.trans
            (by simp [flatStripMotifFlatCost])
  output_space :=
    flatStripMotifResultSpace_le_flatCost width period valid motif
  call continuation bound budget after := by
    rw [Code.flatIterate]
    apply EvaluatorCallFits.fix
    induction motif generalizing valid with
    | nil =>
        let payload := Code.flatStripMotifState width period valid []
        have body := flatStripMotifBodyZero width period valid
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody Code.flatStripMotifStepCode)
                  continuation)
                (flatCountdownOutput Code.flatStripMotifNativeStep
                  0 payload)) := by
          apply EvaluatorExecutionFits.ret_fix_zero
          · rfl
          · simp only [continuationSpace_fix]
            have output := body.output_space
            simp only [flatStripMotifFlatCost] at budget
            simp only [payload] at *
            omega
          · simpa [flatCountdownOutput, payload,
              Code.flatStripMotifState] using after
        exact body.call
          (.fix
            (Code.flatCountdownBody Code.flatStripMotifStepCode)
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              flatStripMotifFlatCost] at *
            exact budget)
          fixedAfter
    | cons cell remaining induction =>
        let nextValid :=
          valid && decide (cell.InStripBounds width period)
        let payload :=
          Code.flatStripMotifState width period valid (cell :: remaining)
        have body :=
          flatStripMotifBodySucc remaining.length width period valid
            cell remaining
        have recursiveBudget :
            flatStripMotifFlatCost width period nextValid remaining +
                continuationSpace continuation ≤
              bound := by
          have raw :
              flatStripMotifFlatCost width period
                    (valid && decide (cell.InStripBounds width period))
                    remaining +
                  continuationSpace continuation ≤
                bound := by
            simp only [flatStripMotifFlatCost] at budget
            omega
          simpa only [nextValid] using raw
        have recursiveAfter :
            EvaluatorExecutionFits bound
              (.ret continuation
                (Code.flatStripMotifState width period
                  (nextValid &&
                    motifInStripBounds width period remaining) [])) := by
          cases valid <;>
            by_cases inBounds : cell.InStripBounds width period <;>
            simpa [nextValid, inBounds] using after
        have recursiveBody :=
          induction nextValid recursiveBudget recursiveAfter
        have fixedAfter :
            EvaluatorExecutionFits bound
              (.ret
                (.fix
                  (Code.flatCountdownBody Code.flatStripMotifStepCode)
                  continuation)
                (flatCountdownOutput Code.flatStripMotifNativeStep
                  (remaining.length + 1) payload)) := by
          apply EvaluatorExecutionFits.ret_fix_succ
          · simp [flatCountdownOutput, payload]
          · simp only [continuationSpace_fix]
            have output := body.output_space
            simp only [flatStripMotifFlatCost] at budget
            simp only [payload, nextValid] at *
            omega
          · simpa [flatCountdownOutput, payload, nextValid] using
              recursiveBody
        exact body.call
          (.fix
            (Code.flatCountdownBody Code.flatStripMotifStepCode)
            continuation)
          bound
          (by
            simp only [continuationSpace_fix,
              flatStripMotifFlatCost] at *
            omega)
          fixedAfter

def flatStripDimensionWidthCost (periodicStrip : PeriodicStrip) : Nat :=
  natPositiveCost periodicStrip.width +
    getCost 0 (PeriodicStripFlatEncoding.stripFields periodicStrip)

theorem flatStripDimensionWidth (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 0))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.width)).toNat]
      (flatStripDimensionWidthCost periodicStrip) := by
  by_cases positive : 0 < periodicStrip.width <;>
    simpa [flatStripDimensionWidthCost, positive,
      PeriodicStripFlatEncoding.stripFields] using
      comp (natPositive periodicStrip.width)
        (get 0 (PeriodicStripFlatEncoding.stripFields periodicStrip))

def flatStripDimensionPeriodCost (periodicStrip : PeriodicStrip) : Nat :=
  natPositiveCost periodicStrip.period +
    getCost 1 (PeriodicStripFlatEncoding.stripFields periodicStrip)

theorem flatStripDimensionPeriod (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 1))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.period)).toNat]
      (flatStripDimensionPeriodCost periodicStrip) := by
  by_cases positive : 0 < periodicStrip.period <;>
    simpa [flatStripDimensionPeriodCost, positive,
      PeriodicStripFlatEncoding.stripFields] using
      comp (natPositive periodicStrip.period)
        (get 1 (PeriodicStripFlatEncoding.stripFields periodicStrip))

def flatStripDimensionsValidCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  boolAndCost fields
    (decide (0 < periodicStrip.width)).toNat
    (decide (0 < periodicStrip.period)).toNat
    (flatStripDimensionWidthCost periodicStrip)
    (flatStripDimensionPeriodCost periodicStrip)

theorem flatStripDimensionsValid (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.stripDimensionsValidCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.width) &&
        decide (0 < periodicStrip.period)).toNat]
      (flatStripDimensionsValidCost periodicStrip) := by
  have fitted :=
    boolAnd (flatStripDimensionWidth periodicStrip)
      (flatStripDimensionPeriod periodicStrip)
  by_cases widthPositive : 0 < periodicStrip.width <;>
    by_cases periodPositive : 0 < periodicStrip.period <;>
    simpa [Code.stripDimensionsValidCode,
      flatStripDimensionsValidCost, widthPositive, periodPositive] using fitted

def flatStripPeriodAndCoordinatesCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let coordinates :=
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [periodicStrip.period] coordinates
    (getCost 1 fields) (dropCost 3 fields)

theorem flatStripPeriodAndCoordinates (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.period ::
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripPeriodAndCoordinatesCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  simpa [flatStripPeriodAndCoordinatesCost, fields, prependCost,
    PeriodicStripFlatEncoding.stripFields] using
    prepend (get 1 fields) (drop 3 fields)

def flatStripDimensionsAndCoordinatesCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let rest := periodicStrip.period ::
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [periodicStrip.width] rest
    (getCost 0 fields) (flatStripPeriodAndCoordinatesCost periodicStrip)

theorem flatStripDimensionsAndCoordinates (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 0) <|
        Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.width :: periodicStrip.period ::
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripDimensionsAndCoordinatesCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  simpa [flatStripDimensionsAndCoordinatesCost, fields, prependCost,
    PeriodicStripFlatEncoding.stripFields] using
    prepend (get 0 fields) (flatStripPeriodAndCoordinates periodicStrip)

def flatStripPayloadCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let rest := periodicStrip.width :: periodicStrip.period ::
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [dimensionsValid.toNat] rest
    (flatStripDimensionsValidCost periodicStrip)
    (flatStripDimensionsAndCoordinatesCost periodicStrip)

theorem flatStripPayload (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
    EvaluatorCodeFits
      (Code.prepend Code.stripDimensionsValidCode <|
        Code.prepend (Code.get 0) <|
          Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        dimensionsValid periodicStrip.motif)
      (flatStripPayloadCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  simpa [flatStripPayloadCost, dimensionsValid, prependCost,
    Code.flatStripMotifState] using
    prepend (flatStripDimensionsValid periodicStrip)
      (flatStripDimensionsAndCoordinates periodicStrip)

def flatStripWellFormedLoopInputCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let payload := Code.flatStripMotifState periodicStrip.width
    periodicStrip.period dimensionsValid periodicStrip.motif
  prependCost fields [periodicStrip.motif.length] payload
    (getCost 2 fields) (flatStripPayloadCost periodicStrip)

theorem flatStripWellFormedLoopInput (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
    EvaluatorCodeFits Code.flatStripWellFormedLoopInputCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.motif.length ::
        Code.flatStripMotifState periodicStrip.width periodicStrip.period
          dimensionsValid periodicStrip.motif)
      (flatStripWellFormedLoopInputCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  simpa [Code.flatStripWellFormedLoopInputCode,
    flatStripWellFormedLoopInputCost, fields, dimensionsValid,
    prependCost, PeriodicStripFlatEncoding.stripFields] using
    prepend (get 2 fields) (flatStripPayload periodicStrip)

def flatStripWellFormedLoopCost (periodicStrip : PeriodicStrip) : Nat :=
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  flatStripMotifFlatCost periodicStrip.width periodicStrip.period
      dimensionsValid periodicStrip.motif +
    flatStripWellFormedLoopInputCost periodicStrip

theorem flatStripWellFormedLoop (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
    EvaluatorCodeFits
      ((Code.flatIterate Code.flatStripMotifStepCode).comp
        Code.flatStripWellFormedLoopInputCode)
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        (dimensionsValid &&
          motifInStripBounds periodicStrip.width periodicStrip.period
            periodicStrip.motif) [])
      (flatStripWellFormedLoopCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  simpa [flatStripWellFormedLoopCost, dimensionsValid] using
    comp
      (flatStripMotifFlat periodicStrip.width periodicStrip.period
        dimensionsValid periodicStrip.motif)
      (flatStripWellFormedLoopInput periodicStrip)

def flatStripWellFormedCost (periodicStrip : PeriodicStrip) : Nat :=
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let result := dimensionsValid &&
    motifInStripBounds periodicStrip.width periodicStrip.period
      periodicStrip.motif
  getCost 0
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        result []) +
    flatStripWellFormedLoopCost periodicStrip

theorem flatStripWellFormed (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.flatStripWellFormedCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [periodicStrip.wellFormed.toNat]
      (flatStripWellFormedCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let result := dimensionsValid &&
    motifInStripBounds periodicStrip.width periodicStrip.period
      periodicStrip.motif
  have fitted :=
    comp
      (get 0
        (Code.flatStripMotifState periodicStrip.width periodicStrip.period
          result []))
      (flatStripWellFormedLoop periodicStrip)
  simpa [Code.flatStripWellFormedCode, flatStripWellFormedCost,
    dimensionsValid, result, Code.stripWellFormedAccumulator_eq] using fitted

set_option maxHeartbeats 1000000 in
theorem flatStripWellFormedLoopInputCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripWellFormedLoopInputCost periodicStrip ≤
      1000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let coordinates :=
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  let inputSpace := encodedListSpace fields
  have inputExpanded :
      inputSpace =
        (Computability.encodeNat periodicStrip.width).length + 1 +
        ((Computability.encodeNat periodicStrip.period).length + 1 +
        ((Computability.encodeNat periodicStrip.motif.length).length + 1 +
          encodedListSpace coordinates)) := by
    simp [inputSpace, fields, coordinates,
      PeriodicStripFlatEncoding.stripFields,
      encodedListSpace_cons]
  have widthSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.width
  have periodSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.period
  have lengthSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.motif.length
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  by_cases widthPositive : 0 < periodicStrip.width <;>
    by_cases periodPositive : 0 < periodicStrip.period <;>
    simp [flatStripWellFormedLoopInputCost, flatStripPayloadCost,
      flatStripDimensionsAndCoordinatesCost,
      flatStripPeriodAndCoordinatesCost,
      flatStripDimensionsValidCost, flatStripDimensionWidthCost,
      flatStripDimensionPeriodCost, natPositiveCost,
      boolAndCost, normalizeBoolCost, prependCost,
      branchZeroZeroCost, branchZeroSuccCost, branchZeroTestCost,
      getCost, dropCost, idCost, headCost, nilCost, oneCost,
      zeroCost, zeroPrimeCost, tailCost, succCost,
      Code.flatStripMotifState, PeriodicStripFlatEncoding.cellFields,
      fields, coordinates, inputSpace, inputExpanded,
      widthPositive, periodPositive, Nat.eq_zero_iff_not_pos,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

theorem flatStripWellFormedProjectionCost_le_input
    (periodicStrip : PeriodicStrip) (result : Bool) :
    getCost 0
        (Code.flatStripMotifState periodicStrip.width periodicStrip.period
          result []) ≤
      1000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputSpace := encodedListSpace fields
  have widthMember : periodicStrip.width ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have periodMember : periodicStrip.period ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have widthSpace := encodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := encodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have widthSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.width
  have periodSuccBits := listCodeEncodeNat_succ_length_le periodicStrip.period
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases result <;>
    simp [getCost, dropCost, idCost, headCost, nilCost,
      zeroPrimeCost, tailCost, succCost,
      Code.flatStripMotifState, fields, inputSpace,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

/-- Complete structural validation, including input preparation and result
projection, is quadratically bounded in the target flat input length. -/
theorem flatStripWellFormedCost_le_quadratic
    (periodicStrip : PeriodicStrip) :
    flatStripWellFormedCost periodicStrip ≤
      2000000000000000000000000000000000000000000000 *
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip) + 1) ^ 2 := by
  let inputSpace :=
    encodedListSpace (PeriodicStripFlatEncoding.stripFields periodicStrip)
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let result := dimensionsValid &&
    motifInStripBounds periodicStrip.width periodicStrip.period
      periodicStrip.motif
  have loop := flatStripMotifFlatCost_le_quadratic
    periodicStrip dimensionsValid
  have prepared := flatStripWellFormedLoopInputCost_le_input periodicStrip
  have projected :=
    flatStripWellFormedProjectionCost_le_input periodicStrip result
  have squareDominates : inputSpace + 1 ≤ (inputSpace + 1) ^ 2 := by
    nlinarith
  simp only [flatStripWellFormedCost, flatStripWellFormedLoopCost,
    dimensionsValid, result, inputSpace] at loop prepared projected ⊢
  nlinarith

end EvaluatorCodeFits

end PartrecToTM2
end Turing
