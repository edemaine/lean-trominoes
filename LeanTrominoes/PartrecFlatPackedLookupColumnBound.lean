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

end EvaluatorCodeFits
end PartrecToTM2
end Turing
