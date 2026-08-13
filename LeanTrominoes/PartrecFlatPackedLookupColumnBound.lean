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

theorem flatLookupHeadBits_le_budget
    (values : List Nat) (budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget) :
    (Computability.encodeNat values.headI).length ≤ budget := by
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  simp only [encodedListSpace_cons, encodedListSpace_nil] at headSpace
  omega

theorem flatLookupHeadSuccBits_le_budget
    (values : List Nat) (budget : Nat)
    (valuesBound : encodedListSpace values ≤ budget)
    (positive : 1 ≤ budget) :
    (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
  cases values with
  | nil =>
      have oneBits : (Computability.encodeNat 1).length = 1 := rfl
      simpa [oneBits] using positive
  | cons value values =>
    have successor := listCodeEncodeNat_succ_length_le value
    have successor' :
        (Computability.encodeNat (value + 1)).length ≤
          (Computability.encodeNat value).length + 1 := by
      simpa [Nat.succ_eq_add_one] using successor
    simp only [List.headI_cons, encodedListSpace_cons] at valuesBound ⊢
    omega

theorem flatLookupBoolAndCost_le_budget
    (values : List Nat)
    (leftValue rightValue leftCost rightCost budget : Nat)
    (leftValueBound : leftValue ≤ 1)
    (rightValueBound : rightValue ≤ 1)
    (valuesBound : encodedListSpace values ≤ budget)
    (leftCostBound : leftCost ≤ budget)
    (rightCostBound : rightCost ≤ budget)
    (positive : 1 ≤ budget) :
    boolAndCost values leftValue rightValue leftCost rightCost ≤
      1000 * (budget + 1) := by
  exact boolAndCost_le_budget values leftValue rightValue
    leftCost rightCost budget leftValueBound rightValueBound valuesBound
    (flatLookupHeadBits_le_budget values budget valuesBound)
    (flatLookupHeadSuccBits_le_budget values budget valuesBound positive)
    leftCostBound rightCostBound positive

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

theorem flatPackedLookupCountSpace_le_unit
    (steps : Nat) (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) (stepsBound : steps ≤ motif.length) :
    encodedListSpace [steps] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : motif.length ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields]
  have lengthSpace := flatLookupEncodedFieldSpace_le_of_mem
    motif.length fields member
  have stepsBits := encodeNat_length_mono stepsBound
  simp only [fields] at lengthSpace
  simp only [encodedListSpace_cons, encodedListSpace_nil,
    flatPackedLookupInputUnit]
  omega

theorem flatPackedLookupCountdownStateSpace_le_unit
    (steps : Nat) (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (stepsBound : steps ≤ motif.length)
    (wordBound : word ≤ wordLimit)
    (digitBound : digit ≤ digitLimit) :
    encodedListSpace
        (steps :: Code.flatPackedLookupColumnState target word digit
          found selected suffix) ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  have bound := flatPackedLookupCountdownStateSpace_le steps target motif
    suffix leading word digit wordLimit digitLimit found selected
    decomposition stepsBound wordBound digitBound
  change encodedListSpace
      (steps :: Code.flatPackedLookupColumnState target word digit
        found selected suffix) ≤
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

theorem flatPackedLookupWordSpace_le_unit
    (target : Cell) (motif : List Cell)
    (word wordLimit digitLimit : Nat) (wordBound : word ≤ wordLimit) :
    encodedListSpace [word] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : wordLimit ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields]
  have limitSpace := flatLookupEncodedFieldSpace_le_of_mem
    wordLimit fields member
  have wordBits := encodeNat_length_mono wordBound
  simp only [fields] at limitSpace
  simp only [encodedListSpace_cons, encodedListSpace_nil,
    flatPackedLookupInputUnit]
  omega

theorem flatPackedLookupDigitSpace_le_unit
    (target : Cell) (motif : List Cell)
    (wordLimit digit digitLimit : Nat) (digitBound : digit ≤ digitLimit) :
    encodedListSpace [digit] ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let fields := flatPackedLookupEnvelopeFields target motif
    wordLimit digitLimit
  have member : digitLimit ∈ fields := by
    simp [fields, flatPackedLookupEnvelopeFields]
  have limitSpace := flatLookupEncodedFieldSpace_le_of_mem
    digitLimit fields member
  have digitBits := encodeNat_length_mono digitBound
  simp only [fields] at limitSpace
  simp only [encodedListSpace_cons, encodedListSpace_nil,
    flatPackedLookupInputUnit]
  omega

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

theorem flatPackedLookupCoordinateMatchCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupCoordinateMatchCost target cell word digit found
        selected remaining ≤
      10000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  let budget := 2000000000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit found selected
        decomposition wordBound digitBound
  have xCost := flatPackedLookupXEqualityCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    found selected decomposition wordBound digitBound
  have yCost := flatPackedLookupYEqualityCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    found selected decomposition wordBound digitBound
  have xValueBound : (decide (cell.1 = target.1)).toNat ≤ 1 := by
    cases decide (cell.1 = target.1) <;> simp
  have yValueBound : (decide (cell.2 = target.2)).toNat ≤ 1 := by
    cases decide (cell.2 = target.2) <;> simp
  have combined := flatLookupBoolAndCost_le_budget state
    (decide (cell.1 = target.1)).toNat
    (decide (cell.2 = target.2)).toNat
    (flatPackedLookupXEqualityCost target cell word digit found selected
      remaining)
    (flatPackedLookupYEqualityCost target cell word digit found selected
      remaining) budget xValueBound yValueBound
    (stateBound.trans (by simp [budget]; omega))
    (by simpa [budget, unit] using xCost)
    (by simpa [budget, unit] using yCost)
    (by simp [budget]; omega)
  simp only [flatPackedLookupCoordinateMatchCost]
  simp only [state, budget, unit] at combined
  omega

theorem flatPackedLookupMatchCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupMatchCost target cell word digit found selected
        remaining ≤
      100000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    found selected (cell :: remaining)
  let budget := 10000000000000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit found selected
        decomposition wordBound digitBound
  have selectedCostRaw := listCodeGetCost_le_linear 5 state
  have selectedCost : getCost 5 state ≤ budget := by
    simp only [budget]
    exact selectedCostRaw.trans (by
      have : encodedListSpace state ≤ unit := stateBound
      omega)
  have coordinate := flatPackedLookupCoordinateMatchCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    found selected decomposition wordBound digitBound
  have selectedValueBound : selected.toNat ≤ 1 := by
    cases selected <;> simp
  have coordinateValueBound : (decide (cell = target)).toNat ≤ 1 := by
    cases decide (cell = target) <;> simp
  have combined := flatLookupBoolAndCost_le_budget state selected.toNat
    (decide (cell = target)).toNat (getCost 5 state)
    (flatPackedLookupCoordinateMatchCost target cell word digit found
      selected remaining) budget selectedValueBound coordinateValueBound
    (stateBound.trans (by simp [budget]; omega)) selectedCost
    (by simpa [budget, unit] using coordinate)
    (by simp [budget]; omega)
  simp only [flatPackedLookupMatchCost]
  simp only [state, budget, unit] at combined
  omega

theorem flatPackedLookupWordStepFieldCost_le_input
    (outputField : Nat) (target cell : Cell)
    (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (outputFieldBound : outputField ≤ 1)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    assignmentWordStepFieldAtCost 2 outputField
        (Code.flatPackedLookupColumnState target word digit found selected
          (cell :: remaining)) ≤
      10000000000000000 *
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
  have wordSpace : encodedListSpace [word] ≤ unit := by
    simpa [unit] using flatPackedLookupWordSpace_le_unit
      target motif word wordLimit digitLimit wordBound
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have remainderBound : word % 9 ≤ wordLimit :=
    (Nat.mod_le word 9).trans wordBound
  have quotientSpace : encodedListSpace [word / 9] ≤ unit := by
    simpa [unit] using flatPackedLookupWordSpace_le_unit
      target motif (word / 9) wordLimit digitLimit quotientBound
  have remainderSpace : encodedListSpace [word % 9] ≤ unit := by
    simpa [unit] using flatPackedLookupWordSpace_le_unit
      target motif (word % 9) wordLimit digitLimit remainderBound
  have pairSpace : encodedListSpace [word / 9, word % 9] ≤ 2 * unit :=
    flatLookupConsSpace_le_of (word / 9) [word % 9] unit
      quotientSpace remainderSpace
  have nineSpace : encodedListSpace [9] ≤ unit := by
    have nineBits : (Computability.encodeNat 9).length = 4 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, nineBits]
    omega
  have argumentOutput : encodedListSpace [word, 9] ≤ 2 * unit :=
    flatLookupConsSpace_le_of word [9] unit wordSpace nineSpace
  have getWordRaw := listCodeGetCost_le_linear 2 state
  have getWord : getCost 2 state ≤ 30000 * (unit + 1) :=
    getWordRaw.trans (by gcongr)
  have zeroState := listCodeZeroCost_le_linear state
  have constantNine := addConstCost_le 9 [0]
  have numeralNine : numeralCost 9 state ≤ 1000000 * (unit + 1) := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp only [numeralCost]
    simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits] at constantNine
    omega
  have arguments := listCodePrependCost_le_of state [word] [9]
    (getCost 2 state) (numeralCost 9 state) (2 * unit)
    (stateBound.trans (by omega)) (wordSpace.trans (by omega)) argumentOutput
  have stateWord : state[2]?.getD 0 = word := by
    simp [state, Code.flatPackedLookupColumnState]
  have argumentsBound :
      assignmentWordStepArgumentsAtCost 2 state ≤
        2000000 * (unit + 1) := by
    rw [assignmentWordStepArgumentsAtCost, stateWord]
    omega
  have division := flatLookupDivisionNineCost_le_budget word unit wordSpace
  have stepBound : assignmentWordStepAtCost 2 state ≤
      2000000000000000 * (unit + 1) := by
    rw [assignmentWordStepAtCost, stateWord]
    omega
  have projectedRaw := listCodeGetCost_le_linear outputField
    [word / 9, word % 9]
  have projected : getCost outputField [word / 9, word % 9] ≤
      20000 * (2 * unit + 1) := by
    have coefficient : 10000 * (outputField + 1) ≤ 20000 := by omega
    have space : encodedListSpace [word / 9, word % 9] + 1 ≤
        2 * unit + 1 := by omega
    exact projectedRaw.trans (Nat.mul_le_mul coefficient space)
  change getCost outputField [word / 9, word % 9] +
      assignmentWordStepAtCost 2 state ≤
    10000000000000000 * unit
  omega

theorem flatPackedLookupContinueCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupContinueCost target cell word digit selected remaining ≤
      100000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let restFields := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  let output := Code.flatPackedLookupColumnState target (word / 9) digit
    false selected remaining
  let out5 := selected.toNat :: restFields
  let out4 := 0 :: out5
  let out3 := digit :: out4
  let out2 := word / 9 :: out3
  let out1 := Encodable.encode target.2 :: out2
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit false selected
        decomposition wordBound digitBound
  have tailDecomposition :
      motif = (leading ++ [cell]) ++ remaining := by
    simpa [List.append_assoc] using decomposition
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have outputBound : encodedListSpace output ≤ unit := by
    simpa [output, unit] using
      flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) digit wordLimit digitLimit
        false selected tailDecomposition quotientBound digitBound
  have out5Bound : encodedListSpace out5 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9, digit, 0] out5
    exact suffix.trans (by
      simpa [output, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out4Bound : encodedListSpace out4 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9, digit] out4
    exact suffix.trans (by
      simpa [output, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out3Bound : encodedListSpace out3 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9] out3
    exact suffix.trans (by
      simpa [output, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out2Bound : encodedListSpace out2 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2] out2
    exact suffix.trans (by
      simpa [output, out2, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out1Bound : encodedListSpace out1 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1] out1
    exact suffix.trans (by
      simpa [output, out1, out2, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have selectedSpace : encodedListSpace [selected.toNat] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have zeroSpace : encodedListSpace [0] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits]
    omega
  have digitSpace : encodedListSpace [digit] ≤ unit := by
    simpa [unit] using flatPackedLookupDigitSpace_le_unit
      target motif wordLimit digit digitLimit digitBound
  have quotientSpace : encodedListSpace [word / 9] ≤ unit := by
    simpa [unit] using flatPackedLookupWordSpace_le_unit
      target motif (word / 9) wordLimit digitLimit quotientBound
  have targetXSpace : encodedListSpace [Encodable.encode target.1] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetXSpace_le_unit
      target motif wordLimit digitLimit
  have targetYSpace : encodedListSpace [Encodable.encode target.2] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetYSpace_le_unit
      target motif wordLimit digitLimit
  have get0Raw := listCodeGetCost_le_linear 0 state
  have get1Raw := listCodeGetCost_le_linear 1 state
  have get3Raw := listCodeGetCost_le_linear 3 state
  have get4Raw := listCodeGetCost_le_linear 4 state
  have get5Raw := listCodeGetCost_le_linear 5 state
  have drop8Raw := flatLookupDropCost_le_linear 8 state
  have get0 : getCost 0 state ≤ 10000 * (unit + 1) :=
    get0Raw.trans (by gcongr)
  have get1 : getCost 1 state ≤ 20000 * (unit + 1) :=
    get1Raw.trans (by gcongr)
  have get3 : getCost 3 state ≤ 40000 * (unit + 1) :=
    get3Raw.trans (by gcongr)
  have get4 : getCost 4 state ≤ 50000 * (unit + 1) :=
    get4Raw.trans (by gcongr)
  have get5 : getCost 5 state ≤ 60000 * (unit + 1) :=
    get5Raw.trans (by gcongr)
  have drop8 : dropCost 8 state ≤ 90000 * (unit + 1) :=
    drop8Raw.trans (by gcongr)
  have wordStep := flatPackedLookupWordStepFieldCost_le_input
    0 target cell motif remaining leading word digit wordLimit digitLimit
    false selected (by omega) decomposition wordBound digitBound
  have wordStepBound : assignmentWordStepFieldAtCost 2 0 state ≤
      10000000000000000 * unit := by
    simpa only [state, unit] using wordStep
  let cost5 := prependCost state [selected.toNat] restFields
    (getCost 5 state) (dropCost 8 state)
  let cost4 := prependCost state [0] out5 (getCost 4 state) cost5
  let cost3 := prependCost state [digit] out4 (getCost 3 state) cost4
  let cost2 := prependCost state [word / 9] out3
    (assignmentWordStepFieldAtCost 2 0 state) cost3
  let cost1 := prependCost state [Encodable.encode target.2] out2
    (getCost 1 state) cost2
  let cost0 := prependCost state [Encodable.encode target.1] out1
    (getCost 0 state) cost1
  have estimate5 := listCodePrependCost_le_of state [selected.toNat]
    restFields (getCost 5 state) (dropCost 8 state) unit
    stateBound selectedSpace out5Bound
  have bound5 : cost5 ≤ 200000 * (unit + 1) := by
    simp only [cost5]
    omega
  have estimate4 := listCodePrependCost_le_of state [0] out5
    (getCost 4 state) cost5 unit stateBound zeroSpace out4Bound
  have bound4 : cost4 ≤ 300000 * (unit + 1) := by
    simp only [cost4]
    omega
  have estimate3 := listCodePrependCost_le_of state [digit] out4
    (getCost 3 state) cost4 unit stateBound digitSpace out3Bound
  have bound3 : cost3 ≤ 400000 * (unit + 1) := by
    simp only [cost3]
    omega
  have estimate2 := listCodePrependCost_le_of state [word / 9] out3
    (assignmentWordStepFieldAtCost 2 0 state) cost3 unit
    stateBound quotientSpace out2Bound
  have bound2 : cost2 ≤ 20000000000000000 * unit := by
    simp only [cost2]
    omega
  have estimate1 := listCodePrependCost_le_of state
    [Encodable.encode target.2] out2 (getCost 1 state) cost2 unit
    stateBound targetYSpace out1Bound
  have bound1 : cost1 ≤ 30000000000000000 * unit := by
    simp only [cost1]
    omega
  have estimate0 := listCodePrependCost_le_of state
    [Encodable.encode target.1] out1 (getCost 0 state) cost1 unit
    stateBound targetXSpace outputBound
  have bound0 : cost0 ≤ 100000000000000000 * unit := by
    simp only [cost0]
    omega
  simpa only [flatPackedLookupContinueCost, state, restFields,
    out5, out4, out3, out2, out1, cost5, cost4, cost3, cost2,
    cost1, cost0, unit] using bound0

theorem flatPackedLookupFoundCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupFoundCost target cell word digit selected remaining ≤
      1000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let restFields := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  let output := Code.flatPackedLookupColumnState target
    (word / 9) (word % 9) true selected remaining
  let out5 := selected.toNat :: restFields
  let out4 := 1 :: out5
  let out3 := word % 9 :: out4
  let out2 := word / 9 :: out3
  let out1 := Encodable.encode target.2 :: out2
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit false selected
        decomposition wordBound digitBound
  have tailDecomposition :
      motif = (leading ++ [cell]) ++ remaining := by
    simpa [List.append_assoc] using decomposition
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have remainderSmall : word % 9 ≤ digitLimit := by
    have remainderLt : word % 9 < 9 := Nat.mod_lt word (by omega)
    omega
  have outputBound : encodedListSpace output ≤ unit := by
    simpa [output, unit] using
      flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) (word % 9) wordLimit digitLimit
        true selected tailDecomposition quotientBound remainderSmall
  have out5Bound : encodedListSpace out5 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9, word % 9, 1] out5
    exact suffix.trans (by
      simpa [output, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out4Bound : encodedListSpace out4 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9, word % 9] out4
    exact suffix.trans (by
      simpa [output, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out3Bound : encodedListSpace out3 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2,
        word / 9] out3
    exact suffix.trans (by
      simpa [output, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out2Bound : encodedListSpace out2 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1, Encodable.encode target.2] out2
    exact suffix.trans (by
      simpa [output, out2, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have out1Bound : encodedListSpace out1 ≤ unit := by
    have suffix := flatLookupEncodedListSpace_suffix_le
      [Encodable.encode target.1] out1
    exact suffix.trans (by
      simpa [output, out1, out2, out3, out4, out5, restFields,
        Code.flatPackedLookupColumnState] using outputBound)
  have selectedSpace : encodedListSpace [selected.toNat] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases selected <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have oneSpace : encodedListSpace [1] ≤ unit := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, oneBits]
    omega
  have remainderSpace : encodedListSpace [word % 9] ≤ unit := by
    simpa [unit] using flatPackedLookupDigitSpace_le_unit
      target motif wordLimit (word % 9) digitLimit remainderSmall
  have quotientSpace : encodedListSpace [word / 9] ≤ unit := by
    simpa [unit] using flatPackedLookupWordSpace_le_unit
      target motif (word / 9) wordLimit digitLimit quotientBound
  have targetXSpace : encodedListSpace [Encodable.encode target.1] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetXSpace_le_unit
      target motif wordLimit digitLimit
  have targetYSpace : encodedListSpace [Encodable.encode target.2] ≤ unit := by
    simpa [unit] using flatPackedLookupTargetYSpace_le_unit
      target motif wordLimit digitLimit
  have get0Raw := listCodeGetCost_le_linear 0 state
  have get1Raw := listCodeGetCost_le_linear 1 state
  have get5Raw := listCodeGetCost_le_linear 5 state
  have drop8Raw := flatLookupDropCost_le_linear 8 state
  have get0 : getCost 0 state ≤ 10000 * (unit + 1) :=
    get0Raw.trans (by gcongr)
  have get1 : getCost 1 state ≤ 20000 * (unit + 1) :=
    get1Raw.trans (by gcongr)
  have get5 : getCost 5 state ≤ 60000 * (unit + 1) :=
    get5Raw.trans (by gcongr)
  have drop8 : dropCost 8 state ≤ 90000 * (unit + 1) :=
    drop8Raw.trans (by gcongr)
  have oneRaw := flatLookupOneCost_le_linear state
  have one : oneCost state ≤ 20000 * (unit + 1) :=
    oneRaw.trans (by gcongr)
  have wordStep0 := flatPackedLookupWordStepFieldCost_le_input
    0 target cell motif remaining leading word digit wordLimit digitLimit
    false selected (by omega) decomposition wordBound digitBound
  have wordStep1 := flatPackedLookupWordStepFieldCost_le_input
    1 target cell motif remaining leading word digit wordLimit digitLimit
    false selected (by omega) decomposition wordBound digitBound
  have wordStep0Bound : assignmentWordStepFieldAtCost 2 0 state ≤
      10000000000000000 * unit := by
    simpa only [state, unit] using wordStep0
  have wordStep1Bound : assignmentWordStepFieldAtCost 2 1 state ≤
      10000000000000000 * unit := by
    simpa only [state, unit] using wordStep1
  let cost5 := prependCost state [selected.toNat] restFields
    (getCost 5 state) (dropCost 8 state)
  let cost4 := prependCost state [1] out5 (oneCost state) cost5
  let cost3 := prependCost state [word % 9] out4
    (assignmentWordStepFieldAtCost 2 1 state) cost4
  let cost2 := prependCost state [word / 9] out3
    (assignmentWordStepFieldAtCost 2 0 state) cost3
  let cost1 := prependCost state [Encodable.encode target.2] out2
    (getCost 1 state) cost2
  let cost0 := prependCost state [Encodable.encode target.1] out1
    (getCost 0 state) cost1
  have estimate5 := listCodePrependCost_le_of state [selected.toNat]
    restFields (getCost 5 state) (dropCost 8 state) unit
    stateBound selectedSpace out5Bound
  have bound5 : cost5 ≤ 200000 * (unit + 1) := by
    simp only [cost5]
    omega
  have estimate4 := listCodePrependCost_le_of state [1] out5
    (oneCost state) cost5 unit stateBound oneSpace out4Bound
  have bound4 : cost4 ≤ 300000 * (unit + 1) := by
    simp only [cost4]
    omega
  have estimate3 := listCodePrependCost_le_of state [word % 9] out4
    (assignmentWordStepFieldAtCost 2 1 state) cost4 unit
    stateBound remainderSpace out3Bound
  have bound3 : cost3 ≤ 20000000000000000 * unit := by
    simp only [cost3]
    omega
  have estimate2 := listCodePrependCost_le_of state [word / 9] out3
    (assignmentWordStepFieldAtCost 2 0 state) cost3 unit
    stateBound quotientSpace out2Bound
  have bound2 : cost2 ≤ 40000000000000000 * unit := by
    simp only [cost2]
    omega
  have estimate1 := listCodePrependCost_le_of state
    [Encodable.encode target.2] out2 (getCost 1 state) cost2 unit
    stateBound targetYSpace out1Bound
  have bound1 : cost1 ≤ 50000000000000000 * unit := by
    simp only [cost1]
    omega
  have estimate0 := listCodePrependCost_le_of state
    [Encodable.encode target.1] out1 (getCost 0 state) cost1 unit
    stateBound targetXSpace outputBound
  have bound0 : cost0 ≤ 1000000000000000000 * unit := by
    simp only [cost0]
    omega
  simpa only [flatPackedLookupFoundCost, state, restFields,
    out5, out4, out3, out2, out1, cost5, cost4, cost3, cost2,
    cost1, cost0, unit] using bound0

theorem flatPackedLookupConsStepCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupConsStepCost target cell word digit selected remaining ≤
      100000000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let continueOutput := Code.flatPackedLookupColumnState target
    (word / 9) digit false selected remaining
  let foundOutput := Code.flatPackedLookupColumnState target
    (word / 9) (word % 9) true selected remaining
  let budget := 100000000000000000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit false selected
        decomposition wordBound digitBound
  have tailDecomposition :
      motif = (leading ++ [cell]) ++ remaining := by
    simpa [List.append_assoc] using decomposition
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have remainderSmall : word % 9 ≤ digitLimit := by
    have remainderLt : word % 9 < 9 := Nat.mod_lt word (by omega)
    omega
  have continueOutputBound : encodedListSpace continueOutput ≤ unit := by
    simpa [continueOutput, unit] using
      flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) digit wordLimit digitLimit
        false selected tailDecomposition quotientBound digitBound
  have foundOutputBound : encodedListSpace foundOutput ≤ unit := by
    simpa [foundOutput, unit] using
      flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) (word % 9) wordLimit digitLimit
        true selected tailDecomposition quotientBound remainderSmall
  have testSpace : encodedListSpace
      [(selected && decide (cell = target)).toNat] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    cases selected && decide (cell = target) <;>
      simp [encodedListSpace_cons, encodedListSpace_nil,
        zeroBits, oneBits] <;> omega
  have matchCost := flatPackedLookupMatchCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    false selected decomposition wordBound digitBound
  have found := flatPackedLookupFoundCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    selected decomposition wordBound digitBound eightBound
  have continuing := flatPackedLookupContinueCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    selected decomposition wordBound digitBound
  have matchBudget : flatPackedLookupMatchCost target cell word digit false
      selected remaining ≤ budget := by
    simpa [budget, unit] using matchCost
  have foundBudget : flatPackedLookupFoundCost target cell word digit selected
      remaining ≤ budget := by
    simp only [budget]
    have := found
    omega
  have continueBudget : flatPackedLookupContinueCost target cell word digit
      selected remaining ≤ budget := by
    simp only [budget]
    have := continuing
    omega
  by_cases hit : selected && decide (cell = target)
  · have branch := flatLookupBranchZeroSuccCost_le_budget state foundOutput
      (selected && decide (cell = target)).toNat
      (flatPackedLookupMatchCost target cell word digit false selected
        remaining)
      (flatPackedLookupFoundCost target cell word digit selected remaining)
      budget (stateBound.trans (by simp [budget]; omega))
      (foundOutputBound.trans (by simp [budget]; omega))
      (testSpace.trans (by simp [budget]; omega)) matchBudget foundBudget
    simp [flatPackedLookupConsStepCost, hit]
    simp [state, foundOutput, budget, unit, hit] at branch
    omega
  · have branch := flatLookupBranchZeroZeroCost_le_budget state continueOutput
      (selected && decide (cell = target)).toNat
      (flatPackedLookupMatchCost target cell word digit false selected
        remaining)
      (flatPackedLookupContinueCost target cell word digit selected remaining)
      budget (stateBound.trans (by simp [budget]; omega))
      (continueOutputBound.trans (by simp [budget]; omega))
      (testSpace.trans (by simp [budget]; omega)) matchBudget continueBudget
    simp [flatPackedLookupConsStepCost, hit]
    simp [state, continueOutput, budget, unit, hit] at branch
    omega

theorem flatPackedLookupStepConsCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupStepConsCost target cell word digit selected remaining ≤
      10000000000000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let output := if selected && decide (cell = target) then
      Code.flatPackedLookupColumnState target (word / 9) (word % 9)
        true selected remaining
    else
      Code.flatPackedLookupColumnState target (word / 9) digit
        false selected remaining
  let budget := 100000000000000000000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif (cell :: remaining)
        leading word digit wordLimit digitLimit false selected
        decomposition wordBound digitBound
  have tailDecomposition :
      motif = (leading ++ [cell]) ++ remaining := by
    simpa [List.append_assoc] using decomposition
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have remainderSmall : word % 9 ≤ digitLimit := by
    have remainderLt : word % 9 < 9 := Nat.mod_lt word (by omega)
    omega
  have outputBound : encodedListSpace output ≤ unit := by
    by_cases hit : selected && decide (cell = target)
    · simp only [output, hit, if_true]
      exact flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) (word % 9) wordLimit digitLimit
        true selected tailDecomposition quotientBound remainderSmall
    · simp only [output, hit]
      exact flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) digit wordLimit digitLimit
        false selected tailDecomposition quotientBound digitBound
  have zeroSpace : encodedListSpace [0] ≤ unit := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, zeroBits]
    omega
  have get4Raw := listCodeGetCost_le_linear 4 state
  have get4 : getCost 4 state ≤ budget := by
    simp only [budget]
    exact get4Raw.trans (by
      have := stateBound
      omega)
  have branchCost := flatPackedLookupConsStepCost_le_input
    target cell motif remaining leading word digit wordLimit digitLimit
    selected decomposition wordBound digitBound eightBound
  have branchBudget : flatPackedLookupConsStepCost target cell word digit
      selected remaining ≤ budget := by
    simpa [budget, unit] using branchCost
  have outer := flatLookupBranchZeroZeroCost_le_budget state output 0
    (getCost 4 state)
    (flatPackedLookupConsStepCost target cell word digit selected remaining)
    budget (stateBound.trans (by simp [budget]; omega))
    (outputBound.trans (by simp [budget]; omega))
    (zeroSpace.trans (by simp [budget]; omega)) get4 branchBudget
  simp only [flatPackedLookupStepConsCost]
  simp only [state, output, budget, unit] at outer
  omega

theorem flatPackedLookupStepFoundCost_le_input
    (target : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupStepFoundCost target word digit selected remaining ≤
      100000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let state := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  let budget := 100000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have stateBound : encodedListSpace state ≤ unit := by
    simpa [state, unit] using
      flatPackedLookupStateSpace_le_unit target motif remaining leading
        word digit wordLimit digitLimit true selected decomposition
        wordBound digitBound
  have oneSpace : encodedListSpace [1] ≤ unit := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, oneBits]
    omega
  have get4Raw := listCodeGetCost_le_linear 4 state
  have get4 : getCost 4 state ≤ budget := by
    simp only [budget]
    exact get4Raw.trans (by
      have := stateBound
      omega)
  have identityRaw := flatLookupIdCost_le_linear state
  have identity : idCost state ≤ budget := by
    simp only [budget]
    exact identityRaw.trans (by
      have := stateBound
      omega)
  have branch := flatLookupBranchZeroSuccCost_le_budget state state 1
    (getCost 4 state) (idCost state) budget
    (stateBound.trans (by simp [budget]; omega))
    (stateBound.trans (by simp [budget]; omega))
    (oneSpace.trans (by simp [budget]; omega)) get4 identity
  simp only [flatPackedLookupStepFoundCost]
  simp only [state, budget, unit] at branch
  omega

theorem flatPackedLookupBodyConsCost_le_input
    (target cell : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ cell :: remaining)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupBodyConsCost remaining.length target cell word digit
        selected remaining ≤
      10000000000000000000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let payload := Code.flatPackedLookupColumnState target word digit
    false selected (cell :: remaining)
  let output := if selected && decide (cell = target) then
      Code.flatPackedLookupColumnState target (word / 9) (word % 9)
        true selected remaining
    else
      Code.flatPackedLookupColumnState target (word / 9) digit
        false selected remaining
  let budget := 10000000000000000000000000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have currentCountBound : remaining.length + 1 ≤ motif.length := by
    rw [decomposition]
    simp
  have predecessorCountBound : remaining.length ≤ motif.length := by omega
  have inputBound : encodedListSpace
      ((remaining.length + 1) :: payload) ≤ unit := by
    simpa [payload, unit] using
      flatPackedLookupCountdownStateSpace_le_unit
        (remaining.length + 1) target motif (cell :: remaining) leading
        word digit wordLimit digitLimit false selected decomposition
        currentCountBound wordBound digitBound
  have predecessorInputBound : encodedListSpace
      (remaining.length :: payload) ≤ unit := by
    simpa [payload, unit] using
      flatPackedLookupCountdownStateSpace_le_unit remaining.length target
        motif (cell :: remaining) leading word digit wordLimit digitLimit
        false selected decomposition predecessorCountBound wordBound digitBound
  have countSpace : encodedListSpace [remaining.length] ≤ unit := by
    simpa [unit] using flatPackedLookupCountSpace_le_unit remaining.length
      target motif wordLimit digitLimit predecessorCountBound
  have tailDecomposition :
      motif = (leading ++ [cell]) ++ remaining := by
    simpa [List.append_assoc] using decomposition
  have quotientBound : word / 9 ≤ wordLimit :=
    (Nat.div_le_self word 9).trans wordBound
  have remainderSmall : word % 9 ≤ digitLimit := by
    have remainderLt : word % 9 < 9 := Nat.mod_lt word (by omega)
    omega
  have outputStateBound : encodedListSpace output ≤ unit := by
    by_cases hit : selected && decide (cell = target)
    · simp only [output, hit, if_true]
      exact flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) (word % 9) wordLimit digitLimit
        true selected tailDecomposition quotientBound remainderSmall
    · simp only [output, hit]
      exact flatPackedLookupStateSpace_le_unit target motif remaining
        (leading ++ [cell]) (word / 9) digit wordLimit digitLimit
        false selected tailDecomposition quotientBound digitBound
  have payloadOutputBound : encodedListSpace
      (remaining.length :: output) ≤ unit := by
    by_cases hit : selected && decide (cell = target)
    · simp only [output, hit, if_true]
      exact flatPackedLookupCountdownStateSpace_le_unit remaining.length
        target motif remaining (leading ++ [cell]) (word / 9) (word % 9)
        wordLimit digitLimit true selected tailDecomposition
        predecessorCountBound quotientBound remainderSmall
    · simp only [output, hit]
      exact flatPackedLookupCountdownStateSpace_le_unit remaining.length
        target motif remaining (leading ++ [cell]) (word / 9) digit
        wordLimit digitLimit false selected tailDecomposition
        predecessorCountBound quotientBound digitBound
  have oneSpace : encodedListSpace [1] ≤ unit := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, oneBits]
    omega
  have taggedOutputBound : encodedListSpace
      (1 :: remaining.length :: output) ≤ 2 * unit :=
    flatLookupConsSpace_le_of 1 (remaining.length :: output) unit
      oneSpace payloadOutputBound
  have stepCost := flatPackedLookupStepConsCost_le_input target cell motif
    remaining leading word digit wordLimit digitLimit selected decomposition
    wordBound digitBound eightBound
  have stepBudget : flatPackedLookupStepConsCost target cell word digit
      selected remaining ≤ budget := by
    simpa [budget, unit] using stepCost
  have body := flatLookupCountdownBodySuccCost_le_budget remaining.length
    payload output
    (flatPackedLookupStepConsCost target cell word digit selected remaining)
    budget
    (inputBound.trans (by simp [budget]; omega))
    (predecessorInputBound.trans (by simp [budget]; omega))
    (countSpace.trans (by simp [budget]; omega))
    (payloadOutputBound.trans (by simp [budget]; omega))
    (taggedOutputBound.trans (by simp [budget]; omega)) stepBudget
  simp only [flatPackedLookupBodyConsCost]
  simp only [payload, output, budget, unit] at body
  omega

theorem flatPackedLookupBodyFoundSuccCost_le_input
    (remainingCount : Nat) (target : Cell)
    (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ remaining)
    (countBound : remainingCount + 1 ≤ motif.length)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupBodyFoundSuccCost remainingCount target word digit
        selected remaining ≤
      100000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let payload := Code.flatPackedLookupColumnState target word digit
    true selected remaining
  let budget := 100000000 * unit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have predecessorCountBound : remainingCount ≤ motif.length := by omega
  have inputBound : encodedListSpace
      ((remainingCount + 1) :: payload) ≤ unit := by
    simpa [payload, unit] using
      flatPackedLookupCountdownStateSpace_le_unit (remainingCount + 1)
        target motif remaining leading word digit wordLimit digitLimit
        true selected decomposition countBound wordBound digitBound
  have predecessorInputBound : encodedListSpace
      (remainingCount :: payload) ≤ unit := by
    simpa [payload, unit] using
      flatPackedLookupCountdownStateSpace_le_unit remainingCount target motif
        remaining leading word digit wordLimit digitLimit true selected
        decomposition predecessorCountBound wordBound digitBound
  have countSpace : encodedListSpace [remainingCount] ≤ unit := by
    simpa [unit] using flatPackedLookupCountSpace_le_unit remainingCount
      target motif wordLimit digitLimit predecessorCountBound
  have oneSpace : encodedListSpace [1] ≤ unit := by
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    simp [encodedListSpace_cons, encodedListSpace_nil, oneBits]
    omega
  have taggedOutputBound : encodedListSpace
      (1 :: remainingCount :: payload) ≤ 2 * unit :=
    flatLookupConsSpace_le_of 1 (remainingCount :: payload) unit
      oneSpace predecessorInputBound
  have stepCost := flatPackedLookupStepFoundCost_le_input target motif
    remaining leading word digit wordLimit digitLimit selected decomposition
    wordBound digitBound
  have stepBudget : flatPackedLookupStepFoundCost target word digit selected
      remaining ≤ budget := by
    simpa [budget, unit] using stepCost
  have body := flatLookupCountdownBodySuccCost_le_budget remainingCount
    payload payload
    (flatPackedLookupStepFoundCost target word digit selected remaining)
    budget
    (inputBound.trans (by simp [budget]; omega))
    (predecessorInputBound.trans (by simp [budget]; omega))
    (countSpace.trans (by simp [budget]; omega))
    (predecessorInputBound.trans (by simp [budget]; omega))
    (taggedOutputBound.trans (by simp [budget]; omega)) stepBudget
  simp only [flatPackedLookupBodyFoundSuccCost]
  simp only [payload, budget, unit] at body
  omega

theorem flatPackedLookupBodyZeroCost_le_input
    (target : Cell) (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found selected : Bool)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupBodyZeroCost
        (Code.flatPackedLookupColumnState target word digit found selected
          suffix) ≤
      10 * flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  let payload := Code.flatPackedLookupColumnState target word digit
    found selected suffix
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  have inputBound : encodedListSpace (0 :: payload) ≤ unit := by
    simpa [payload, unit] using
      flatPackedLookupCountdownStateSpace_le_unit 0 target motif suffix leading
        word digit wordLimit digitLimit found selected decomposition
        (by omega) wordBound digitBound
  have body := flatLookupCountdownBodyZeroCost_le_budget payload unit inputBound
  simpa only [flatPackedLookupBodyZeroCost, payload, unit] using
    body.trans (by omega)

/-- The exact frozen suffix pays one uniformly bounded body per remaining
countdown step. -/
theorem flatPackedLookupFoundFlatCost_le_input_mul
    (steps : Nat) (target : Cell) (motif remaining leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (selected : Bool)
    (decomposition : motif = leading ++ remaining)
    (stepsBound : steps ≤ remaining.length)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit) :
    flatPackedLookupFoundFlatCost steps target word digit selected remaining ≤
      100000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit *
        (steps + 1) := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  induction steps with
  | zero =>
      have body := flatPackedLookupBodyZeroCost_le_input target motif
        remaining leading word digit wordLimit digitLimit true selected
        decomposition wordBound digitBound
      simp only [flatPackedLookupFoundFlatCost]
      omega
  | succ steps induction =>
      have countBound : steps + 1 ≤ motif.length := by
        have suffixLength : remaining.length ≤ motif.length := by
          rw [decomposition]
          simp
        omega
      have body := flatPackedLookupBodyFoundSuccCost_le_input steps target
        motif remaining leading word digit wordLimit digitLimit selected
        decomposition countBound wordBound digitBound
      have tail := induction (by omega)
      simp only [flatPackedLookupFoundFlatCost]
      nlinarith

/-- The exact consuming recurrence costs one bounded body per coordinate,
switching to the frozen recurrence after the first selected hit. -/
theorem flatPackedLookupFlatCost_false_le_input_mul
    (target : Cell) (selected : Bool)
    (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupFlatCost target selected suffix word digit false ≤
      100000000000000000000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit *
        (suffix.length + 1) := by
  let unit := flatPackedLookupInputUnit target motif wordLimit digitLimit
  have unitPositive : 5 ≤ unit := by
    simp [unit, flatPackedLookupInputUnit]
  induction suffix generalizing leading word digit with
  | nil =>
      have body := flatPackedLookupBodyZeroCost_le_input target motif []
        leading word digit wordLimit digitLimit false selected decomposition
        wordBound digitBound
      simp only [flatPackedLookupFlatCost, List.length_nil,
        Nat.zero_add, Nat.mul_one]
      omega
  | cons cell remaining induction =>
      have tailDecomposition :
          motif = (leading ++ [cell]) ++ remaining := by
        simpa [List.append_assoc] using decomposition
      have quotientBound : word / 9 ≤ wordLimit :=
        (Nat.div_le_self word 9).trans wordBound
      have remainderSmall : word % 9 ≤ digitLimit := by
        have remainderLt : word % 9 < 9 := Nat.mod_lt word (by omega)
        omega
      have body := flatPackedLookupBodyConsCost_le_input target cell motif
        remaining leading word digit wordLimit digitLimit selected decomposition
        wordBound digitBound eightBound
      by_cases hit : selected && decide (cell = target)
      · have frozen := flatPackedLookupFoundFlatCost_le_input_mul
          remaining.length target motif remaining (leading ++ [cell])
          (word / 9) (word % 9) wordLimit digitLimit selected
          tailDecomposition (by rfl) quotientBound remainderSmall
        simp [flatPackedLookupFlatCost, hit]
        nlinarith
      · have tail := induction (leading ++ [cell]) (word / 9) digit
          tailDecomposition quotientBound digitBound
        simp [flatPackedLookupFlatCost, hit]
        nlinarith

theorem flatPackedLookupFlatCost_le_input_mul
    (target : Cell) (selected : Bool)
    (motif suffix leading : List Cell)
    (word digit wordLimit digitLimit : Nat) (found : Bool)
    (decomposition : motif = leading ++ suffix)
    (wordBound : word ≤ wordLimit) (digitBound : digit ≤ digitLimit)
    (eightBound : 8 ≤ digitLimit) :
    flatPackedLookupFlatCost target selected suffix word digit found ≤
      100000000000000000000000000000000000 *
        flatPackedLookupInputUnit target motif wordLimit digitLimit *
        (suffix.length + 1) := by
  cases found with
  | false =>
      exact flatPackedLookupFlatCost_false_le_input_mul target selected motif
        suffix leading word digit wordLimit digitLimit decomposition
        wordBound digitBound eightBound
  | true =>
      have frozen := flatPackedLookupFoundFlatCost_le_input_mul suffix.length
        target motif suffix leading word digit wordLimit digitLimit selected
        decomposition (by rfl) wordBound digitBound
      simpa only [flatPackedLookupFlatCost] using frozen.trans (by
        have unitPositive : 1 ≤
            flatPackedLookupInputUnit target motif wordLimit digitLimit := by
          simp [flatPackedLookupInputUnit]
        nlinarith)

/-- Each motif cell contributes two delimited native coordinate fields, so
the motif cardinality is bounded by its flat coordinate footprint. -/
theorem flatPackedLookupMotifLength_le_coordinateSpace
    (motif : List Cell) :
    motif.length ≤ encodedListSpace
      (motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  induction motif with
  | nil => simp
  | cons cell motif induction =>
      simp [PeriodicStripFlatEncoding.cellFields,
        encodedListSpace_cons] at induction ⊢
      omega

theorem flatPackedLookupMotifLength_le_inputUnit
    (target : Cell) (motif : List Cell)
    (wordLimit digitLimit : Nat) :
    motif.length + 1 ≤
      flatPackedLookupInputUnit target motif wordLimit digitLimit := by
  have lengthBound := flatPackedLookupMotifLength_le_coordinateSpace motif
  have coordinatesBound := flatLookupEncodedListSpace_suffix_le
    [motif.length, Encodable.encode target.1, Encodable.encode target.2,
      wordLimit, digitLimit]
    (motif.flatMap PeriodicStripFlatEncoding.cellFields)
  simp only [flatPackedLookupInputUnit,
    flatPackedLookupEnvelopeFields]
  omega

/-- Quadratic envelope for one complete native-field motif-column pass. -/
def flatPackedLookupSpaceBound
    (target : Cell) (motif : List Cell) (word digit : Nat) : Nat :=
  100000000000000000000000000000000000 *
    (flatPackedLookupInputUnit target motif word (digit + 8)) ^ 2

theorem flatPackedLookupFlatCost_le_quadratic
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    flatPackedLookupFlatCost target selected motif word digit found ≤
      flatPackedLookupSpaceBound target motif word digit := by
  have additive := flatPackedLookupFlatCost_le_input_mul target selected
    motif motif [] word digit word (digit + 8) found (by simp)
    (by omega) (by omega) (by omega)
  have factor := flatPackedLookupMotifLength_le_inputUnit
    target motif word (digit + 8)
  calc
    flatPackedLookupFlatCost target selected motif word digit found ≤
        100000000000000000000000000000000000 *
          flatPackedLookupInputUnit target motif word (digit + 8) *
          (motif.length + 1) := additive
    _ ≤ 100000000000000000000000000000000000 *
          flatPackedLookupInputUnit target motif word (digit + 8) *
          flatPackedLookupInputUnit target motif word (digit + 8) := by
      exact Nat.mul_le_mul_left _ factor
    _ = flatPackedLookupSpaceBound target motif word digit := by
      simp [flatPackedLookupSpaceBound, pow_two, Nat.mul_assoc]

/-- Actual countdown-plus-payload footprint presented to the flat iterator. -/
def flatPackedLookupNativeInputSpace
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) : Nat :=
  encodedListSpace
      (motif.length :: Code.flatPackedLookupColumnState target word digit
        found selected motif) + 1

theorem flatPackedLookupInputUnit_le_native
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    flatPackedLookupInputUnit target motif word (digit + 8) ≤
      10 * flatPackedLookupNativeInputSpace
        target selected motif word digit found := by
  have digitBits := encodeNat_add_length_le_sum digit 8
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have eightBits : (Computability.encodeNat 8).length = 4 := rfl
  rw [eightBits] at digitBits
  cases found <;> cases selected <;>
    simp [flatPackedLookupInputUnit, flatPackedLookupEnvelopeFields,
      flatPackedLookupNativeInputSpace,
      Code.flatPackedLookupColumnState, encodedListSpace_cons,
      zeroBits, oneBits] <;>
    omega

/-- The one-pass evaluator allowance is quadratic in the bit footprint of its
actual native flat input. -/
theorem flatPackedLookupSpaceBound_le_native_quadratic
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    flatPackedLookupSpaceBound target motif word digit ≤
      10000000000000000000000000000000000000 *
        (flatPackedLookupNativeInputSpace
          target selected motif word digit found) ^ 2 := by
  let unit := flatPackedLookupInputUnit target motif word (digit + 8)
  let native := flatPackedLookupNativeInputSpace
    target selected motif word digit found
  have linear : unit ≤ 10 * native := by
    simpa [unit, native] using flatPackedLookupInputUnit_le_native
      target selected motif word digit found
  have squared : unit ^ 2 ≤ 100 * native ^ 2 := by
    nlinarith
  calc
    flatPackedLookupSpaceBound target motif word digit =
        100000000000000000000000000000000000 * unit ^ 2 := by
      rfl
    _ ≤ 100000000000000000000000000000000000 *
          (100 * native ^ 2) := Nat.mul_le_mul_left _ squared
    _ = 10000000000000000000000000000000000000 *
          native ^ 2 := by ring

/-- One complete flat lookup pass fitted directly to its quadratic native
input allowance. -/
theorem flatPackedLookupFlatBounded
    (target : Cell) (selected : Bool) (motif : List Cell)
    (word digit : Nat) (found : Bool) :
    EvaluatorCodeFits
      (Code.flatIterate Code.flatPackedLookupStepCode)
      (motif.length ::
        Code.flatPackedLookupColumnState target word digit found selected
          motif)
      (Code.flatPackedLookupColumnProcess target selected motif
        word digit found)
      (flatPackedLookupSpaceBound target motif word digit) :=
  (flatPackedLookupFlat target selected motif word digit found).mono
    (flatPackedLookupFlatCost_le_quadratic
      target selected motif word digit found)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
