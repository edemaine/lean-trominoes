import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PartrecPowerTwoSpace
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PartrecFlatStripCycleSpace
import LeanTrominoes.PartrecFlatStripDecider

/-!
# Polynomial-space certificate for the native-flat strip decider

The only new unbounded pass is the streaming computation of the target input
length.  Its accumulator plus the unconsumed suffix always equals the original
flat-list footprint, so every iteration has a uniform linear workspace bound.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState
namespace FlatStripDeciderPartrec

open Computability
open LeanTrominoes.FiniteState
open Turing ToPartrec PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

attribute [-simp] PeriodicStripFlatEncoding.finEncoding_encode_length

/-! ## Streaming target-length computation -/

def encodedListSpaceStepCost (values : List Nat) : Nat :=
  let accumulator := values[0]?.getD 0
  let field := values[1]?.getD 0
  let length := LeanTrominoes.Computability.binaryEncodingLength field
  let increment := length + 1
  let lengthCost := binaryEncodingLengthCost field + getCost 1 values
  let incrementCost := addConstCost 1 [length] + lengthCost
  let argumentsCost := prependCost values [accumulator] [increment]
    (getCost 0 values) incrementCost
  let sumCost := natAddCost accumulator increment + argumentsCost
  prependCost values [accumulator + increment] (values.drop 2)
    sumCost (dropCost 2 values)

theorem encodedListSpaceStep_fits (values : List Nat) :
    EvaluatorCodeFits encodedListSpaceStepCode values
      (encodedListSpaceStep values) (encodedListSpaceStepCost values) := by
  let accumulator := values[0]?.getD 0
  let field := values[1]?.getD 0
  let length := LeanTrominoes.Computability.binaryEncodingLength field
  let increment := length + 1
  have lengthFit := EvaluatorCodeFits.comp
    (binaryEncodingLengthCode field) (get 1 values)
  have incrementFit := EvaluatorCodeFits.comp
    (addConst 1 [length]) lengthFit
  have argumentsFit := prepend (get 0 values) incrementFit
  have sumFit := EvaluatorCodeFits.comp
    (natAdd accumulator increment) argumentsFit
  have result := prepend sumFit (drop 2 values)
  simpa [encodedListSpaceStepCode, encodedListSpaceStep,
    encodedListSpaceStepCost, accumulator, field, length, increment,
    prependCost, Nat.add_assoc] using result

/-- Reachable states of the streaming fold split into an accumulated prefix
footprint and an unconsumed suffix whose sum is the original footprint. -/
def EncodedListSpaceInvariant (fields : List Nat)
    (remaining : Nat) (payload : List Nat) : Prop :=
  ∃ accumulator suffix,
    payload = accumulator :: suffix ∧
    remaining = suffix.length ∧
    accumulator + encodedListSpace suffix = encodedListSpace fields

theorem encodedListSpaceInvariant_initial (fields : List Nat) :
    EncodedListSpaceInvariant fields fields.length (0 :: fields) := by
  exact ⟨0, fields, rfl, rfl, by simp⟩

theorem encodedListSpaceInvariant_preserved
    (fields : List Nat) (remaining : Nat) (payload : List Nat)
    (invariant : EncodedListSpaceInvariant fields (remaining + 1) payload) :
    EncodedListSpaceInvariant fields remaining
      (encodedListSpaceStep payload) := by
  obtain ⟨accumulator, suffix, rfl, lengthEq, spaceEq⟩ := invariant
  cases suffix with
  | nil => simp at lengthEq
  | cons field suffix =>
      refine ⟨accumulator + (Computability.encodeNat field).length + 1,
        suffix, ?_, ?_, ?_⟩
      · simp [encodedListSpaceStep]
      · simp at lengthEq
        omega
      · rw [encodedListSpace_cons] at spaceEq
        omega

def encodedListSpaceStepSpaceBound (inputLength : Nat) : Nat :=
  10000000000000000 * (inputLength + 10)

theorem encodedListSpaceStepCost_le
    (fields : List Nat) (remaining : Nat) (values : List Nat)
    (invariant : EncodedListSpaceInvariant fields remaining values) :
    encodedListSpaceStepCost values ≤
      encodedListSpaceStepSpaceBound (encodedListSpace fields) := by
  obtain ⟨accumulator, suffix, rfl, remainingEq, spaceEq⟩ := invariant
  let inputLength := encodedListSpace fields
  let field := suffix[0]?.getD 0
  let length := LeanTrominoes.Computability.binaryEncodingLength field
  let increment := length + 1
  have suffixBound : encodedListSpace suffix ≤ inputLength := by
    simp only [inputLength] at spaceEq ⊢
    omega
  have accumulatorBound : accumulator ≤ inputLength := by
    simp only [inputLength] at spaceEq ⊢
    omega
  have accumulatorBits := encodeNat_length_le_self accumulator
  have valuesSpace : encodedListSpace (accumulator :: suffix) ≤
      inputLength + 1 := by
    rw [encodedListSpace_cons]
    omega
  have fieldSpace : encodedListSpace [field] ≤ inputLength + 1 := by
    have raw := StripSavitchStep.singletonGetDSpace_le 0 suffix
    exact raw.trans (by omega)
  have fieldBits : (Computability.encodeNat field).length ≤ inputLength := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at fieldSpace
    omega
  have lengthEq : length = (Computability.encodeNat field).length := by
    simp [length]
  have lengthBound : length ≤ inputLength := by omega
  have lengthBits := encodeNat_length_le_self length
  have lengthSpace : encodedListSpace [length] ≤ inputLength + 1 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have incrementBound : increment ≤ inputLength + 1 := by
    simp only [increment]
    omega
  have incrementBits := encodeNat_length_le_self increment
  have incrementSpace : encodedListSpace [increment] ≤ inputLength + 2 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have incrementSuffixBound : increment ≤ encodedListSpace suffix + 1 := by
    have raw := StripSavitchStep.singletonGetDSpace_le 0 suffix
    simp only [encodedListSpace_cons, encodedListSpace_nil] at raw
    simp only [increment, length,
      LeanTrominoes.Computability.binaryEncodingLength_eq]
    omega
  have accumulatorSpace : encodedListSpace [accumulator] ≤ inputLength + 1 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have sumBound : accumulator + increment ≤ inputLength + 1 := by
    omega
  have sumBits := encodeNat_length_le_self (accumulator + increment)
  have sumSpace : encodedListSpace [accumulator + increment] ≤
      inputLength + 2 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have tailBound : encodedListSpace ((accumulator :: suffix).drop 2) ≤
      inputLength := by
    cases suffix with
    | nil =>
        change 0 ≤ inputLength
        exact Nat.zero_le _
    | cons head tail =>
        have tailSpace :=
          Turing.PartrecToTM2.EvaluatorCodeFits.listCodeEncodedListSpace_tail_le
            (head :: tail)
        exact tailSpace.trans suffixBound
  have get0 := listCodeGetCost_le_linear 0 (accumulator :: suffix)
  have get1 := listCodeGetCost_le_linear 1 (accumulator :: suffix)
  have drop2 := StripSavitchStep.dropCost_le_linear 2 (accumulator :: suffix)
  have lengthCost : binaryEncodingLengthCost field ≤
      10000000000000 * (inputLength + 2) := by
    simp only [binaryEncodingLengthCost]
    omega
  have addCost := addConstCost_le 1 [length]
  have addCost' : addConstCost 1 [length] ≤
      2000 * (inputLength + 3) := by
    exact addCost.trans (by
      simp only [Nat.reduceAdd, Nat.reduceMul]
      omega)
  have addition := natAddCost_le_linear accumulator increment
  have limitBits := encodeNat_length_le_self
    (2 * (accumulator + increment) + 4)
  have limitSpace : encodedListSpace
      [2 * (accumulator + increment) + 4] + 1 ≤
        2 * inputLength + 8 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  have addition' : natAddCost accumulator increment ≤
      100000000 * (2 * inputLength + 8) :=
    addition.trans (Nat.mul_le_mul_left _ limitSpace)
  dsimp only [field, length, increment] at *
  simp only [encodedListSpaceStepCost]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.headI_cons, prependCost,
    encodedListSpace_cons, encodedListSpace_nil,
    encodedListSpaceStepSpaceBound]
  omega

def encodedListSpaceLoopSpaceBound (inputLength : Nat) : Nat :=
  100000 * (encodedListSpaceStepSpaceBound inputLength + inputLength + 10)

private theorem listLength_le_encodedListSpace (values : List Nat) :
    values.length ≤ encodedListSpace values := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.length_cons, encodedListSpace_cons]
      omega

theorem encodedListSpaceBodyCost_le
    (fields : List Nat) (remaining : Nat) (payload : List Nat)
    (invariant : EncodedListSpaceInvariant fields remaining payload) :
    flatCountdownBodyCost encodedListSpaceStep encodedListSpaceStepCost
        remaining payload ≤
      encodedListSpaceLoopSpaceBound (encodedListSpace fields) := by
  obtain ⟨accumulator, suffix, rfl, remainingEq, spaceEq⟩ := invariant
  let inputLength := encodedListSpace fields
  have accumulatorBound : accumulator ≤ inputLength := by
    omega
  have accumulatorBits := encodeNat_length_le_self accumulator
  have inputLengthBits := encodeNat_length_le_self inputLength
  have payloadSpace : encodedListSpace (accumulator :: suffix) ≤
      inputLength + 1 := by
    simp only [inputLength] at spaceEq ⊢
    rw [encodedListSpace_cons]
    omega
  have stepCost := encodedListSpaceStepCost_le fields remaining
    (accumulator :: suffix) ⟨accumulator, suffix, rfl, remainingEq, spaceEq⟩
  have stepOutput := (encodedListSpaceStep_fits
    (accumulator :: suffix)).output_space
  have remainingBound : remaining ≤ inputLength := by
    have suffixLength := listLength_le_encodedListSpace suffix
    omega
  have remainingBits := listCodeEncodeNat_length_mono remainingBound
  have remainingSuccBits := listCodeEncodeNat_succ_length_le remaining
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases remaining with
  | zero =>
      simp [flatCountdownBodyCost, encodedListSpaceLoopSpaceBound,
        zeroPrimeCost, encodedListSpace_cons, zeroBits]
      omega
  | succ remaining =>
      have predecessorBits := listCodeEncodeNat_length_mono
        (show remaining ≤ remaining + 1 by omega)
      simp [flatCountdownBodyCost, flatCountdownSuccBranchCost,
        encodedListSpaceLoopSpaceBound, prependCost, tailCost,
        headCost, oneCost, zeroCost, nilCost, idCost, zeroPrimeCost,
        succCost, encodedListSpace_cons, zeroBits, oneBits] at *
      omega

/-- The streaming fold itself fits a uniform polynomial reserve in the
original flat-list footprint. -/
theorem encodedListSpaceLoop_fits (fields : List Nat) :
    EvaluatorCodeFits (Code.flatIterate encodedListSpaceStepCode)
      (fields.length :: 0 :: fields) [encodedListSpace fields]
      (encodedListSpaceLoopSpaceBound (encodedListSpace fields)) := by
  let inputLength := encodedListSpace fields
  have fieldCount := listLength_le_encodedListSpace fields
  have fieldCountBits := encodeNat_length_le_self fields.length
  have inputLengthBits := encodeNat_length_le_self inputLength
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have inputSpace : encodedListSpace (fields.length :: 0 :: fields) ≤
      encodedListSpaceLoopSpaceBound inputLength := by
    simp [encodedListSpaceLoopSpaceBound, encodedListSpaceStepSpaceBound,
      encodedListSpace_cons, inputLength, zeroBits]
    omega
  have outputSpace : encodedListSpace [inputLength] ≤
      encodedListSpaceLoopSpaceBound inputLength := by
    simp [encodedListSpaceLoopSpaceBound, encodedListSpaceStepSpaceBound,
      encodedListSpace_cons]
    omega
  refine
    { input_space := inputSpace
      output_space := outputSpace
      call := ?_ }
  intro continuation bound budget after
  have bodyFits : ∀ remaining payload,
      EvaluatorCodeFits (Code.flatCountdownBody encodedListSpaceStepCode)
        (remaining :: payload)
        (flatCountdownOutput encodedListSpaceStep remaining payload)
        (flatCountdownBodyCost encodedListSpaceStep
          encodedListSpaceStepCost remaining payload) := by
    intro remaining payload
    exact flatCountdownBody (fun payload => encodedListSpaceStep_fits payload)
      remaining payload
  apply EvaluatorCallFits.flatIterate_of_code_fits_invariant
      bodyFits (encodedListSpaceInvariant_initial fields)
      (encodedListSpaceInvariant_preserved fields)
  · intro remaining payload invariant
    have localCost :=
      encodedListSpaceBodyCost_le fields remaining payload invariant
    omega
  · simpa [encodedListSpaceStep_iterate,
      encodedListSpace_eq_fieldPayloadSpace] using after

/-! ## Native input preparation and complete streamed length -/

def flatStripFieldCountCost (values : List Nat) : Nat :=
  let motifLength := values[2]?.getD 0
  let argumentsCost := prependCost values [motifLength] [motifLength]
    (getCost 2 values) (getCost 2 values)
  let doubleCost := natAddCost motifLength motifLength + argumentsCost
  addConstCost 3 [motifLength + motifLength] + doubleCost

theorem flatStripFieldCount_fits (values : List Nat) :
    EvaluatorCodeFits flatStripFieldCountCode values
      [values[2]?.getD 0 + values[2]?.getD 0 + 3]
      (flatStripFieldCountCost values) := by
  let motifLength := values[2]?.getD 0
  have arguments := prepend (get 2 values) (get 2 values)
  have doubled := EvaluatorCodeFits.comp
    (natAdd motifLength motifLength) arguments
  have result := EvaluatorCodeFits.comp
    (addConst 3 [motifLength + motifLength]) doubled
  simpa [flatStripFieldCountCode, flatStripFieldCountCost, motifLength,
    prependCost] using result

def flatStripEncodedListSpaceInputCost (values : List Nat) : Nat :=
  let motifLength := values[2]?.getD 0
  let restCost := prependCost values [0] values
    (zeroCost values) (idCost values)
  prependCost values
    [motifLength + motifLength + 3] (0 :: values)
    (flatStripFieldCountCost values) restCost

theorem flatStripEncodedListSpaceInput_fits
    (periodicStrip : PeriodicStrip) :
    let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
    EvaluatorCodeFits flatStripEncodedListSpaceInputCode fields
      (fields.length :: 0 :: fields)
      (flatStripEncodedListSpaceInputCost fields) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  change EvaluatorCodeFits flatStripEncodedListSpaceInputCode fields
    (fields.length :: 0 :: fields)
    (flatStripEncodedListSpaceInputCost fields)
  have getMotifLength : fields[2]?.getD 0 = periodicStrip.motif.length := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have fieldsLength : fields.length = 3 + 2 * periodicStrip.motif.length := by
    simpa [fields] using
      PeriodicStripFlatEncoding.stripFields_length periodicStrip
  have result := prepend (flatStripFieldCount_fits fields)
    (prepend (zero fields) (id fields))
  have countEq : fields[2]?.getD 0 + fields[2]?.getD 0 + 3 =
      fields.length := by
    rw [getMotifLength, fieldsLength]
    omega
  rw [countEq] at result
  simpa [flatStripEncodedListSpaceInputCode,
    flatStripEncodedListSpaceInputCost, countEq, prependCost] using result

def flatStripEncodedListSpaceCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  encodedListSpaceLoopSpaceBound (encodedListSpace fields) +
    flatStripEncodedListSpaceInputCost fields

/-- The public native-field length program has a complete evaluator-space
certificate, not just a semantic evaluation theorem. -/
theorem flatStripEncodedListSpace_fits (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits flatStripEncodedListSpaceCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length]
      (flatStripEncodedListSpaceCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  have result := EvaluatorCodeFits.comp
    (encodedListSpaceLoop_fits fields)
    (flatStripEncodedListSpaceInput_fits periodicStrip)
  simpa [flatStripEncodedListSpaceCode, flatStripEncodedListSpaceCost, fields,
    PeriodicStripFlatEncoding.finEncoding_encode_length,
    encodedListSpace_eq_sum] using result

/-! ## Savitch depth and padded state bound -/

def flatStripSearchDepthInputCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  prependCost fields [inputLength] [1]
    (flatStripEncodedListSpaceCost periodicStrip) (oneCost fields)

theorem flatStripSearchDepthInput_fits (periodicStrip : PeriodicStrip) :
    let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
    let inputLength :=
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
    EvaluatorCodeFits flatStripSearchDepthInputCode fields
      [inputLength, 1] (flatStripSearchDepthInputCost periodicStrip) := by
  simpa [flatStripSearchDepthInputCode, flatStripSearchDepthInputCost,
    prependCost] using
    prepend (flatStripEncodedListSpace_fits periodicStrip)
      (one (PeriodicStripFlatEncoding.stripFields periodicStrip))

def SearchDepthInvariant (steps remaining : Nat)
    (payload : List Nat) : Prop :=
  ∃ processed,
    processed + remaining = steps ∧
      payload = ((Code.addConstListStep 21)^[processed]) [1]

theorem searchDepthInvariant_initial (steps : Nat) :
    SearchDepthInvariant steps steps [1] := by
  exact ⟨0, by simp, rfl⟩

theorem searchDepthInvariant_preserved
    (steps remaining : Nat) (payload : List Nat)
    (invariant : SearchDepthInvariant steps (remaining + 1) payload) :
    SearchDepthInvariant steps remaining
      (Code.addConstListStep 21 payload) := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  refine ⟨processed + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply']

def flatStripSearchDepthLoopCost (inputLength : Nat) : Nat :=
  1000000000000 * (inputLength + 1)

theorem flatStripSearchDepthBodyCost_le
    (inputLength remaining : Nat) (payload : List Nat)
    (invariant : SearchDepthInvariant inputLength remaining payload) :
    binaryLengthAffine21BodyCost remaining payload ≤
      flatStripSearchDepthLoopCost inputLength := by
  obtain ⟨processed, sum, rfl⟩ := invariant
  have processedBound : processed ≤ inputLength := by omega
  have remainingBound : remaining ≤ inputLength := by omega
  have remainingBits := encodeNat_length_le_self remaining
  have currentBits := encodeNat_length_le_self (1 + processed * 21)
  have nextBits := encodeNat_length_le_self (1 + (processed + 1) * 21)
  have currentList := Code.addConstListStep_iterate 21 processed 1
  have nextList := Code.addConstListStep_iterate 21 (processed + 1) 1
  have nextPayload :
      Code.addConstListStep 21
          (((Code.addConstListStep 21)^[processed]) [1]) =
        ((Code.addConstListStep 21)^[processed + 1]) [1] := by
    rw [Function.iterate_succ_apply']
  have bodyBound := binaryLengthAffine21BodyCost_le remaining
    (((Code.addConstListStep 21)^[processed]) [1])
  rw [nextPayload, currentList, nextList] at bodyBound
  simp only [encodedListSpace_cons, encodedListSpace_nil] at bodyBound
  rw [currentList]
  apply bodyBound.trans
  unfold flatStripSearchDepthLoopCost
  omega

theorem flatStripSearchDepthLoop_fits (inputLength : Nat) :
    EvaluatorCodeFits (Code.flatIterate (Code.addConst 21))
      [inputLength, 1] [1 + inputLength * 21]
      (flatStripSearchDepthLoopCost inputLength) := by
  have inputLengthBits := encodeNat_length_le_self inputLength
  have outputBits := encodeNat_length_le_self (1 + inputLength * 21)
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have inputSpace : encodedListSpace [inputLength, 1] ≤
      flatStripSearchDepthLoopCost inputLength := by
    simp [flatStripSearchDepthLoopCost, encodedListSpace_cons, oneBits]
    omega
  have outputSpace : encodedListSpace [1 + inputLength * 21] ≤
      flatStripSearchDepthLoopCost inputLength := by
    simp [flatStripSearchDepthLoopCost, encodedListSpace_cons]
    omega
  refine
    { input_space := inputSpace
      output_space := outputSpace
      call := ?_ }
  intro continuation bound budget after
  apply EvaluatorCallFits.flatIterate_of_code_fits_invariant
      binaryLengthAffine21Body (searchDepthInvariant_initial inputLength)
      (searchDepthInvariant_preserved inputLength)
  · intro remaining payload invariant
    have localCost := flatStripSearchDepthBodyCost_le
      inputLength remaining payload invariant
    omega
  · simpa [Code.addConstListStep_iterate] using after

def flatStripSearchDepthCost (periodicStrip : PeriodicStrip) : Nat :=
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  flatStripSearchDepthLoopCost inputLength +
    flatStripSearchDepthInputCost periodicStrip

theorem flatStripSearchDepth_fits (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits flatStripSearchDepthCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [flatStripSearchDepth periodicStrip]
      (flatStripSearchDepthCost periodicStrip) := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have result := EvaluatorCodeFits.comp
    (flatStripSearchDepthLoop_fits inputLength)
    (flatStripSearchDepthInput_fits periodicStrip)
  have outputEq : 1 + inputLength * 21 =
      flatStripSearchDepth periodicStrip := by
    simp [flatStripSearchDepth, inputLength]
    omega
  rw [outputEq] at result
  simpa [flatStripSearchDepthCode, flatStripSearchDepthCost,
    inputLength] using result

def flatStripStateBoundCost (periodicStrip : PeriodicStrip) : Nat :=
  powerTwoCost (flatStripSearchDepth periodicStrip) +
    flatStripSearchDepthCost periodicStrip

theorem flatStripStateBound_fits (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits flatStripStateBoundCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [flatStripStateBound periodicStrip]
      (flatStripStateBoundCost periodicStrip) := by
  simpa [flatStripStateBoundCode, flatStripStateBoundCost,
    flatStripStateBound] using
    EvaluatorCodeFits.comp
      (powerTwo (flatStripSearchDepth periodicStrip))
      (flatStripSearchDepth_fits periodicStrip)

def flatStripCycleParametersCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let depth := flatStripSearchDepth periodicStrip
  let stateBound := flatStripStateBound periodicStrip
  let restCost := prependCost fields [depth] fields
    (flatStripSearchDepthCost periodicStrip) (idCost fields)
  prependCost fields [stateBound] (depth :: fields)
    (flatStripStateBoundCost periodicStrip) restCost

/-- Complete search-parameter assembly retains the native fields after the
computed padded state bound and depth. -/
theorem flatStripCycleParameters_fits (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits flatStripCycleParametersCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      ([flatStripStateBound periodicStrip,
          flatStripSearchDepth periodicStrip] ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      (flatStripCycleParametersCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  have result := prepend (flatStripStateBound_fits periodicStrip)
    (prepend (flatStripSearchDepth_fits periodicStrip) (id fields))
  simpa [flatStripCycleParametersCode, flatStripCycleParametersCost,
    fields, prependCost] using result

end FlatStripDeciderPartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
