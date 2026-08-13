import LeanTrominoes.PartrecFlatPackedLookupColumnSpace

/-!
# Native-field bounds for flat packed lookup

The exact evaluator certificates retain an unconsumed suffix of the motif's
coordinate fields.  This module establishes one fixed envelope, expressed in
the original native fields, for every suffix state and countdown input reached
during a lookup pass.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

theorem flatLookupEncodedFieldSpace_le_of_mem
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

theorem flatLookupEncodedListSpace_suffix_le
    (leadingFields suffix : List Nat) :
    encodedListSpace suffix ≤
      encodedListSpace (leadingFields ++ suffix) := by
  induction leadingFields with
  | nil => simp
  | cons value leadingFields induction =>
      rw [List.cons_append, encodedListSpace_cons]
      exact induction.trans (by omega)

theorem flatLookupEncodedListSpace_prefix_le
    (prefixFields suffix : List Nat) :
    encodedListSpace prefixFields ≤
      encodedListSpace (prefixFields ++ suffix) := by
  induction prefixFields with
  | nil => simp
  | cons value prefixFields induction =>
      rw [List.cons_append, encodedListSpace_cons,
        encodedListSpace_cons]
      omega

/-- Original native fields against which a complete lookup pass is charged. -/
def flatPackedLookupEnvelopeFields
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) : List Nat :=
  [motif.length, Encodable.encode target.1, Encodable.encode target.2,
    wordLimit, digitLimit] ++
      motif.flatMap PeriodicStripFlatEncoding.cellFields

theorem flatPackedLookupSuffixSpace_le
    (motif suffix leading : List Cell)
    (decomposition : motif = leading ++ suffix) :
    encodedListSpace
        (suffix.flatMap PeriodicStripFlatEncoding.cellFields) ≤
      encodedListSpace
        (motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have bound := flatLookupEncodedListSpace_suffix_le
    (leading.flatMap PeriodicStripFlatEncoding.cellFields)
    suffixFields
  simpa [decomposition, suffixFields, List.flatMap_append] using bound

/-- Every reachable scanner payload fits in the original native envelope plus
the two Boolean flag cells. -/
theorem flatPackedLookupStateSpace_le
    (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (Code.flatPackedLookupColumnState target word digit found selected
          suffix) ≤
      encodedListSpace
          (flatPackedLookupEnvelopeFields target motif
            wordLimit digitLimit) + 4 := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  let targetX := Encodable.encode target.1
  let targetY := Encodable.encode target.2
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have suffixSpace := flatPackedLookupSuffixSpace_le motif suffix
    leading decomposition
  have inputExpanded :
      encodedListSpace fields =
        (Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat targetX).length + 1 +
        ((Computability.encodeNat targetY).length + 1 +
        ((Computability.encodeNat wordLimit).length + 1 +
        ((Computability.encodeNat digitLimit).length + 1 +
          encodedListSpace
            (motif.flatMap PeriodicStripFlatEncoding.cellFields))))) := by
    simp [fields, flatPackedLookupEnvelopeFields, targetX, targetY,
      encodedListSpace_cons]
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitBound
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;> cases selected <;>
    simp [Code.flatPackedLookupColumnState,
      encodedListSpace_cons, fields, targetX, targetY,
      zeroBits, oneBits] at inputExpanded suffixSpace ⊢ <;>
    omega

/-- Adding a bounded countdown field still changes the native envelope by
only a constant number of cells. -/
theorem flatPackedLookupCountdownStateSpace_le
    (steps : Nat) (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (stepsBound : steps ≤ motif.length)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (steps :: Code.flatPackedLookupColumnState target word digit
          found selected suffix) ≤
      encodedListSpace
          (flatPackedLookupEnvelopeFields target motif
            wordLimit digitLimit) + 4 := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  let targetX := Encodable.encode target.1
  let targetY := Encodable.encode target.2
  let suffixFields := suffix.flatMap PeriodicStripFlatEncoding.cellFields
  have suffixSpace := flatPackedLookupSuffixSpace_le motif suffix
    leading decomposition
  have inputExpanded :
      encodedListSpace fields =
        (Computability.encodeNat motif.length).length + 1 +
        ((Computability.encodeNat targetX).length + 1 +
        ((Computability.encodeNat targetY).length + 1 +
        ((Computability.encodeNat wordLimit).length + 1 +
        ((Computability.encodeNat digitLimit).length + 1 +
          encodedListSpace
            (motif.flatMap PeriodicStripFlatEncoding.cellFields))))) := by
    simp [fields, flatPackedLookupEnvelopeFields, targetX, targetY,
      encodedListSpace_cons]
  have stepsBits := encodeNat_length_mono stepsBound
  have wordBits := encodeNat_length_mono wordBound
  have digitBits := encodeNat_length_mono digitBound
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases found <;> cases selected <;>
    simp [Code.flatPackedLookupColumnState,
      encodedListSpace_cons, fields, targetX, targetY,
      zeroBits, oneBits] at inputExpanded suffixSpace ⊢ <;>
    omega

/-! ## Reusable fixed-code cost estimates -/

theorem flatLookupIdCost_le_linear (values : List Nat) :
    idCost values ≤ 10 * (encodedListSpace values + 1) := by
  have tailSpace := listCodeEncodedListSpace_tail_le (0 :: values)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp [idCost, tailCost, zeroPrimeCost,
    encodedListSpace_cons, zeroBits] at tailSpace ⊢
  omega

theorem flatLookupOneCost_le_linear (values : List Nat) :
    oneCost values ≤ 20000 * (encodedListSpace values + 1) := by
  have zeroBound := listCodeZeroCost_le_linear values
  have successor := succCost_le [0]
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  simp only [oneCost]
  simp [encodedListSpace_cons, zeroBits] at successor
  omega

theorem flatLookupDropCost_le_linear
    (index : Nat) (values : List Nat) :
    dropCost index values ≤
      (10000 * (index + 1)) * (encodedListSpace values + 1) := by
  have whole := listCodeGetCost_le_linear index values
  have part : dropCost index values ≤ getCost index values := by
    simp only [getCost]
    omega
  exact part.trans whole

theorem flatLookupSingletonPredSpace_le (value : Nat) :
    encodedListSpace [value.pred] ≤ encodedListSpace [value] := by
  simp only [encodedListSpace_cons, encodedListSpace_nil]
  exact Nat.add_le_add_right
    (listCodeEncodeNat_length_mono (Nat.pred_le value)) 1

theorem flatLookupConsSpace_le_of
    (value : Nat) (values : List Nat) (budget : Nat)
    (valueBound : encodedListSpace [value] ≤ budget)
    (valuesBound : encodedListSpace values ≤ budget) :
    encodedListSpace (value :: values) ≤ 2 * budget := by
  simp only [encodedListSpace_cons, encodedListSpace_nil] at *
  omega

theorem flatLookupPrependCost_le_budget
    (values fieldOutput restOutput : List Nat)
    (fieldCost restCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (fieldBound : encodedListSpace fieldOutput ≤ budget)
    (outputBound :
      encodedListSpace (fieldOutput.headI :: restOutput) ≤ budget)
    (fieldCostBound : fieldCost ≤ budget)
    (restCostBound : restCost ≤ budget) :
    prependCost values fieldOutput restOutput fieldCost restCost ≤
      5 * (budget + 1) := by
  have estimate := listCodePrependCost_le_of values fieldOutput restOutput
    fieldCost restCost budget valuesBound fieldBound outputBound
  omega

theorem flatLookupBranchZeroZeroCost_le_budget
    (values output : List Nat)
    (testValue testCost branchCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (outputBound : encodedListSpace output ≤ budget)
    (testValueBound : encodedListSpace [testValue] ≤ budget)
    (testCostBound : testCost ≤ budget)
    (branchCostBound : branchCost ≤ budget) :
    branchZeroZeroCost values output testValue testCost branchCost ≤
      40 * (budget + 1) := by
  have testedInput := flatLookupConsSpace_le_of
    testValue values budget testValueBound valuesBound
  have identity := flatLookupIdCost_le_linear values
  have testHead : [testValue].headI = testValue := by simp
  simp only [branchZeroZeroCost, branchZeroTestCost, prependCost]
  rw [testHead]
  omega

theorem flatLookupBranchZeroSuccCost_le_budget
    (values output : List Nat)
    (testValue testCost branchCost budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (outputBound : encodedListSpace output ≤ budget)
    (testValueBound : encodedListSpace [testValue] ≤ budget)
    (testCostBound : testCost ≤ budget)
    (branchCostBound : branchCost ≤ budget) :
    branchZeroSuccCost values output testValue testCost branchCost ≤
      50 * (budget + 1) := by
  have testedInput := flatLookupConsSpace_le_of
    testValue values budget testValueBound valuesBound
  have predecessorBound := flatLookupSingletonPredSpace_le testValue
  have predecessorInput := flatLookupConsSpace_le_of
    testValue.pred values budget (predecessorBound.trans testValueBound)
      valuesBound
  have identity := flatLookupIdCost_le_linear values
  have tail := listCodeTailCost_le_linear (testValue.pred :: values)
  have testHead : [testValue].headI = testValue := by simp
  simp only [branchZeroSuccCost, branchZeroTestCost, prependCost]
  rw [testHead]
  omega

/-- Natural equality remains linear when both operands fit in a shared native
field budget. -/
theorem flatLookupNatEqCost_le_budget
    (left right budget : Nat)
    (leftBound : encodedListSpace [left] ≤ budget)
    (rightBound : encodedListSpace [right] ≤ budget) :
    natEqCost left right ≤
      1000000000000 * (budget + 1) := by
  have equality := natEqCost_le_linear left right
  have sumBits := encodeNat_add_length_le_sum left right
  have scaledBits := encodeNat_mul_length_le_sum 2 (left + right)
  have finalBits := encodeNat_add_length_le_sum
    (2 * (left + right)) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := rfl
  have fourBits : (Computability.encodeNat 4).length = 3 := rfl
  rw [twoBits] at scaledBits
  rw [fourBits] at finalBits
  simp only [encodedListSpace_cons, encodedListSpace_nil] at equality leftBound rightBound
  omega

/-- Division by nine, as used to consume one packed assignment digit, remains
linear in any budget containing the dividend. -/
theorem flatLookupDivisionNineCost_le_budget
    (number budget : Nat)
    (numberBound : encodedListSpace [number] ≤ budget) :
    divisionSpaceBound number 9 ≤
      1000000000000000 * (budget + 1) := by
  have sumBits := encodeNat_add_length_le_sum number 9
  have scaledBits := encodeNat_mul_length_le_sum 8 (number + 9)
  have finalBits := encodeNat_add_length_le_sum
    (8 * (number + 9)) 16
  have eightBits : (Computability.encodeNat 8).length = 4 := rfl
  have nineBits : (Computability.encodeNat 9).length = 4 := rfl
  have sixteenBits : (Computability.encodeNat 16).length = 5 := rfl
  rw [eightBits] at scaledBits
  rw [nineBits] at sumBits
  rw [sixteenBits] at finalBits
  simp only [divisionSpaceBound, encodedListSpace_cons,
    encodedListSpace_nil] at numberBound ⊢
  omega

/-- A positive flat-countdown body has a fixed linear overhead once its input,
step output, and step cost share one workspace budget. -/
theorem flatLookupCountdownSuccBranchCost_le_budget
    (remaining : Nat) (payload output : List Nat)
    (stepCost budget : Nat)
    (valuesBound :
      encodedListSpace (remaining :: payload) ≤ budget)
    (remainingBound : encodedListSpace [remaining] ≤ budget)
    (payloadOutputBound :
      encodedListSpace (remaining :: output) ≤ budget)
    (taggedOutputBound :
      encodedListSpace (1 :: remaining :: output) ≤ budget)
    (stepCostBound : stepCost ≤ budget) :
    flatCountdownSuccBranchCost (fun _ => output) (fun _ => stepCost)
        remaining payload ≤
      30000 * (budget + 1) := by
  have tail := listCodeTailCost_le_linear (remaining :: payload)
  have head := headCost_le (remaining :: payload)
  have one := flatLookupOneCost_le_linear (remaining :: payload)
  have transformed :
      stepCost + tailCost (remaining :: payload) ≤
        4 * (budget + 1) := by
    omega
  have payloadCost := listCodePrependCost_le_of
    (remaining :: payload) [remaining] output
      (headCost (remaining :: payload))
      (stepCost + tailCost (remaining :: payload)) budget
      valuesBound remainingBound
      payloadOutputBound
  have payloadCostBound :
      prependCost (remaining :: payload) [remaining] output
          (headCost (remaining :: payload))
          (stepCost + tailCost (remaining :: payload)) ≤
        1010 * (budget + 1) := by
    omega
  have oneSpace : encodedListSpace [1] ≤ budget := by
    have prefixBound : encodedListSpace [1] ≤
        encodedListSpace (1 :: remaining :: output) := by
      simp only [encodedListSpace_cons, encodedListSpace_nil]
      omega
    exact prefixBound.trans taggedOutputBound
  have outer := listCodePrependCost_le_of
    (remaining :: payload) [1] (remaining :: output)
      (oneCost (remaining :: payload))
      (prependCost (remaining :: payload) [remaining] output
        (headCost (remaining :: payload))
        (stepCost + tailCost (remaining :: payload))) budget
      valuesBound oneSpace taggedOutputBound
  simp only [flatCountdownSuccBranchCost]
  omega

theorem flatLookupCountdownBodyZeroCost_le_budget
    (payload : List Nat) (budget : Nat)
    (inputBound : encodedListSpace (0 :: payload) ≤ budget) :
    flatCountdownBodyCost (fun _ => payload) (fun _ => 0) 0 payload ≤
      5 * (budget + 1) := by
  have payloadBound := listCodeEncodedListSpace_tail_le (0 :: payload)
  simp [flatCountdownBodyCost, zeroPrimeCost] at inputBound ⊢
  omega

theorem flatLookupCountdownBodySuccCost_le_budget
    (remaining : Nat) (payload output : List Nat)
    (stepCost budget : Nat)
    (inputBound :
      encodedListSpace ((remaining + 1) :: payload) ≤ budget)
    (predecessorInputBound :
      encodedListSpace (remaining :: payload) ≤ budget)
    (remainingBound : encodedListSpace [remaining] ≤ budget)
    (payloadOutputBound :
      encodedListSpace (remaining :: output) ≤ budget)
    (taggedOutputBound :
      encodedListSpace (1 :: remaining :: output) ≤ budget)
    (stepCostBound : stepCost ≤ budget) :
    flatCountdownBodyCost (fun _ => output) (fun _ => stepCost)
        (remaining + 1) payload ≤
      30010 * (budget + 1) := by
  have branch := flatLookupCountdownSuccBranchCost_le_budget
    remaining payload output stepCost budget predecessorInputBound
    remainingBound payloadOutputBound taggedOutputBound
    stepCostBound
  simp only [flatCountdownBodyCost]
  omega

/-! ## Lookup-component bounds -/

/-- One positive native-field allowance for a complete lookup pass and all of
its reachable suffix states. -/
def flatPackedLookupInputUnit
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) : Nat :=
  encodedListSpace
    (flatPackedLookupEnvelopeFields target motif wordLimit digitLimit) + 5

theorem flatPackedLookupStateSpace_le_unit
    (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (Code.flatPackedLookupColumnState target word digit found selected
          suffix) ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  have bound := flatPackedLookupStateSpace_le target motif suffix leading
    word digit wordLimit digitLimit found selected decomposition
    wordBound digitBound
  change encodedListSpace
      (Code.flatPackedLookupColumnState target word digit found selected
        suffix) ≤
    encodedListSpace
      (flatPackedLookupEnvelopeFields target motif wordLimit digitLimit) + 5
  omega

theorem flatPackedLookupTargetXSpace_le_unit
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) :
    encodedListSpace [Encodable.encode target.1] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : Encodable.encode target.1 ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields]
  have bound := flatLookupEncodedFieldSpace_le_of_mem
    (Encodable.encode target.1) fields member
  have widened :
      (Computability.encodeNat (Encodable.encode target.1)).length + 1 ≤
        encodedListSpace fields + 5 := by omega
  simpa [flatPackedLookupInputUnit, fields,
    encodedListSpace_cons, encodedListSpace_nil] using widened

theorem flatPackedLookupTargetYSpace_le_unit
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) :
    encodedListSpace [Encodable.encode target.2] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : Encodable.encode target.2 ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields]
  have bound := flatLookupEncodedFieldSpace_le_of_mem
    (Encodable.encode target.2) fields member
  have widened :
      (Computability.encodeNat (Encodable.encode target.2)).length + 1 ≤
        encodedListSpace fields + 5 := by omega
  simpa [flatPackedLookupInputUnit, fields,
    encodedListSpace_cons, encodedListSpace_nil] using widened

theorem flatPackedLookupCellXSpace_le_unit
    (target cell : Cell) (motif remaining leading : List Cell)
    (wordLimit digitLimit : Nat)
    (decomposition : motif = leading ++ cell :: remaining) :
    encodedListSpace [Encodable.encode cell.1] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : Encodable.encode cell.1 ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields, decomposition,
      PeriodicStripFlatEncoding.cellFields]
  have bound := flatLookupEncodedFieldSpace_le_of_mem
    (Encodable.encode cell.1) fields member
  have widened :
      (Computability.encodeNat (Encodable.encode cell.1)).length + 1 ≤
        encodedListSpace fields + 5 := by omega
  simpa [flatPackedLookupInputUnit, fields,
    encodedListSpace_cons, encodedListSpace_nil] using widened

theorem flatPackedLookupCellYSpace_le_unit
    (target cell : Cell) (motif remaining leading : List Cell)
    (wordLimit digitLimit : Nat)
    (decomposition : motif = leading ++ cell :: remaining) :
    encodedListSpace [Encodable.encode cell.2] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : Encodable.encode cell.2 ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields, decomposition,
      PeriodicStripFlatEncoding.cellFields]
  have bound := flatLookupEncodedFieldSpace_le_of_mem
    (Encodable.encode cell.2) fields member
  have widened :
      (Computability.encodeNat (Encodable.encode cell.2)).length + 1 ≤
        encodedListSpace fields + 5 := by omega
  simpa [flatPackedLookupInputUnit, fields,
    encodedListSpace_cons, encodedListSpace_nil] using widened

theorem flatPackedLookupXEqualityArgumentsCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupXEqualityArgumentsCost target cell word digit found
        selected remaining ≤
      1000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit found selected
        decomposition wordBound digitBound
  have cellXBound : encodedListSpace [Encodable.encode cell.1] ≤ unit := by
    simpa [unit] using flatPackedLookupCellXSpace_le_unit
      target cell motif remaining leading wordLimit digitLimit decomposition
  have targetXBound : encodedListSpace [Encodable.encode target.1] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetXSpace_le_unit
      target motif wordLimit digitLimit
  have pairBound : encodedListSpace
      [Encodable.encode cell.1, Encodable.encode target.1] ≤ 2 * unit :=
    flatLookupConsSpace_le_of (Encodable.encode cell.1)
      [Encodable.encode target.1] unit cellXBound targetXBound
  have getCell := listCodeGetCost_le_linear 6 state
  have getTarget := listCodeGetCost_le_linear 0 state
  have getCellBound : getCost 6 state ≤ 70000 * (unit + 1) := by
    exact getCell.trans (by gcongr)
  have getTargetBound : getCost 0 state ≤ 10000 * (unit + 1) := by
    exact getTarget.trans (by gcongr)
  have estimate := listCodePrependCost_le_of state
    [Encodable.encode cell.1] [Encodable.encode target.1]
    (getCost 6 state) (getCost 0 state) (2 * unit)
    (stateBound.trans (by omega)) (cellXBound.trans (by omega)) pairBound
  change prependCost state [Encodable.encode cell.1]
      [Encodable.encode target.1] (getCost 6 state) (getCost 0 state) ≤
    1000000 * unit
  omega

theorem flatPackedLookupXEqualityCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupXEqualityCost target cell word digit found selected
        remaining ≤
      2000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have cellXBound : encodedListSpace [Encodable.encode cell.1] ≤ unit := by
    simpa [unit] using flatPackedLookupCellXSpace_le_unit
      target cell motif remaining leading wordLimit digitLimit decomposition
  have targetXBound : encodedListSpace [Encodable.encode target.1] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetXSpace_le_unit
      target motif wordLimit digitLimit
  have equality := flatLookupNatEqCost_le_budget
    (Encodable.encode cell.1) (Encodable.encode target.1) unit
    cellXBound targetXBound
  have arguments := flatPackedLookupXEqualityArgumentsCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    found selected decomposition wordBound digitBound
  simp only [flatPackedLookupXEqualityCost]
  simp only [unit] at equality arguments
  omega

theorem flatPackedLookupYEqualityArgumentsCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupYEqualityArgumentsCost target cell word digit found
        selected remaining ≤
      1000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit found selected
        decomposition wordBound digitBound
  have cellYBound : encodedListSpace [Encodable.encode cell.2] ≤ unit := by
    simpa [unit] using flatPackedLookupCellYSpace_le_unit
      target cell motif remaining leading wordLimit digitLimit decomposition
  have targetYBound : encodedListSpace [Encodable.encode target.2] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetYSpace_le_unit
      target motif wordLimit digitLimit
  have pairBound : encodedListSpace
      [Encodable.encode cell.2, Encodable.encode target.2] ≤ 2 * unit :=
    flatLookupConsSpace_le_of (Encodable.encode cell.2)
      [Encodable.encode target.2] unit cellYBound targetYBound
  have getCell := listCodeGetCost_le_linear 7 state
  have getTarget := listCodeGetCost_le_linear 1 state
  have getCellBound : getCost 7 state ≤ 80000 * (unit + 1) := by
    exact getCell.trans (by gcongr)
  have getTargetBound : getCost 1 state ≤ 20000 * (unit + 1) := by
    exact getTarget.trans (by gcongr)
  have estimate := listCodePrependCost_le_of state
    [Encodable.encode cell.2] [Encodable.encode target.2]
    (getCost 7 state) (getCost 1 state) (2 * unit)
    (stateBound.trans (by omega)) (cellYBound.trans (by omega)) pairBound
  change prependCost state [Encodable.encode cell.2]
      [Encodable.encode target.2] (getCost 7 state) (getCost 1 state) ≤
    1000000 * unit
  omega

theorem flatPackedLookupYEqualityCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupYEqualityCost target cell word digit found selected
        remaining ≤
      2000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have cellYBound : encodedListSpace [Encodable.encode cell.2] ≤ unit := by
    simpa [unit] using flatPackedLookupCellYSpace_le_unit
      target cell motif remaining leading wordLimit digitLimit decomposition
  have targetYBound : encodedListSpace [Encodable.encode target.2] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetYSpace_le_unit
      target motif wordLimit digitLimit
  have equality := flatLookupNatEqCost_le_budget
    (Encodable.encode cell.2) (Encodable.encode target.2) unit
    cellYBound targetYBound
  have arguments := flatPackedLookupYEqualityArgumentsCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    found selected decomposition wordBound digitBound
  simp only [flatPackedLookupYEqualityCost]
  simp only [unit] at equality arguments
  omega

end EvaluatorCodeFits
end PartrecToTM2
end Turing
