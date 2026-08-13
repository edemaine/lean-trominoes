import LeanTrominoes.PartrecAddSpace
import LeanTrominoes.PartrecBinaryLengthSpace
import LeanTrominoes.PartrecPowerTwoSpace
import LeanTrominoes.PartrecFlatIterationSpace
import LeanTrominoes.PartrecFlatFieldPolySpace
import LeanTrominoes.PartrecPairSpace
import LeanTrominoes.PartrecStripCellBoundsSpace
import LeanTrominoes.PartrecFlatStripCycleSpace
import LeanTrominoes.PartrecFlatStripDecider
import LeanTrominoes.PeriodicStripFlatEncodingSize

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

/-! ## Structural guard -/

private theorem guardEncodedFieldSpace_le_of_mem
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

private theorem guardEncodedListSpace_suffix_le
    (leadingFields suffix : List Nat) :
    encodedListSpace suffix ≤
      encodedListSpace (leadingFields ++ suffix) := by
  rw [LeanTrominoes.FiniteState.encodedListSpace_append]
  omega

def flatStripGuardStepCost
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) : Nat :=
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let xCode := Encodable.encode cell.1
  let yCode := Encodable.encode cell.2
  let cellCode := Encodable.encode cell
  let rest := remaining.flatMap PeriodicStripFlatEncoding.cellFields
  let pairArgumentsCost := prependCost state [xCode] [yCode]
    (getCost 3 state) (getCost 4 state)
  let cellCost := natPairCost xCode yCode + pairArgumentsCost
  let periodAndCellCost := prependCost state [period] [cellCode]
    (getCost 2 state) cellCost
  let cellArgumentsCost := prependCost state [width] [period, cellCode]
    (getCost 1 state) periodAndCellCost
  let inBoundsCost := stripCellInBoundsCost width period cell +
    cellArgumentsCost
  let cellTag := if cell.InStripBounds width period then 1 else 0
  let updatedValidCost := boolAndCost state valid.toNat cellTag
    (getCost 0 state) inBoundsCost
  let periodAndRestCost := prependCost state [period] rest
    (getCost 2 state) (dropCost 5 state)
  let dimensionsAndRestCost := prependCost state [width] (period :: rest)
    (getCost 1 state) periodAndRestCost
  let nextValid := valid && decide (cell.InStripBounds width period)
  prependCost state [nextValid.toNat] (width :: period :: rest)
    updatedValidCost dimensionsAndRestCost

theorem flatStripGuardStep_fits
    (width period : Nat) (valid : Bool)
    (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits Code.flatStripMotifStepCode
      (Code.flatStripMotifState width period valid (cell :: remaining))
      (Code.flatStripMotifState width period
        (valid && decide (cell.InStripBounds width period)) remaining)
      (flatStripGuardStepCost width period valid cell remaining) := by
  let state :=
    Code.flatStripMotifState width period valid (cell :: remaining)
  let xCode := Encodable.encode cell.1
  let yCode := Encodable.encode cell.2
  have pairArguments := prepend (get 3 state) (get 4 state)
  have cellFit := EvaluatorCodeFits.comp (natPair xCode yCode) pairArguments
  have periodAndCell := prepend (get 2 state) cellFit
  have cellArguments := prepend (get 1 state) periodAndCell
  have inBounds := EvaluatorCodeFits.comp
    (stripCellInBounds width period cell) cellArguments
  have updatedValid := boolAnd (get 0 state) inBounds
  have periodAndRest := prepend (get 2 state) (drop 5 state)
  have dimensionsAndRest := prepend (get 1 state) periodAndRest
  have result := prepend updatedValid dimensionsAndRest
  rcases cell with ⟨x, y⟩
  cases valid <;>
    by_cases inBoundsH : Cell.InStripBounds width period (x, y) <;>
    simpa [Code.flatStripMotifStepCode,
      Code.flatStripMotifUpdatedValidCode,
      Code.flatStripMotifHeadInBoundsCode,
      Code.flatStripMotifCellArgumentsCode,
      Code.flatStripMotifCellCode,
      Code.flatStripMotifCellPairArgumentsCode,
      flatStripGuardStepCost, state, xCode, yCode,
      Code.flatStripMotifState,
      PeriodicStripFlatEncoding.cellFields,
      inBoundsH, prependCost] using result

def flatStripGuardBodyCost
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) : Nat :=
  let nextState := Code.flatStripMotifState width period
    (valid && decide (cell.InStripBounds width period)) remaining
  flatCountdownBodyCost (fun _ => nextState)
    (fun _ => flatStripGuardStepCost width period valid cell remaining)
    remainingCount
    (Code.flatStripMotifState width period valid (cell :: remaining))

theorem flatStripGuardBodySucc_fits
    (remainingCount width period : Nat)
    (valid : Bool) (cell : Cell) (remaining : List Cell) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      ((remainingCount + 1) ::
        Code.flatStripMotifState width period valid (cell :: remaining))
      (flatCountdownOutput (fun _ => Code.flatStripMotifState width period
          (valid && decide (cell.InStripBounds width period)) remaining)
        (remainingCount + 1)
        (Code.flatStripMotifState width period valid (cell :: remaining)))
      (flatStripGuardBodyCost (remainingCount + 1)
        width period valid cell remaining) := by
  have body := flatCountdownBody_of_fit
    (flatStripGuardStep_fits width period valid cell remaining)
    (remainingCount + 1)
  simpa [flatStripGuardBodyCost] using body

def flatStripGuardBodyZeroCost
    (width period : Nat) (valid : Bool) : Nat :=
  flatCountdownBodyCost Code.flatStripMotifNativeStep
    (fun _ => 0) 0 (Code.flatStripMotifState width period valid [])

theorem flatStripGuardBodyZero_fits
    (width period : Nat) (valid : Bool) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      (0 :: Code.flatStripMotifState width period valid [])
      (flatCountdownOutput Code.flatStripMotifNativeStep 0
        (Code.flatStripMotifState width period valid []))
      (flatStripGuardBodyZeroCost width period valid) := by
  simpa [Code.flatCountdownBody, flatCountdownOutput,
    flatStripGuardBodyZeroCost, flatCountdownBodyCost,
    zeroPrimeCost] using
    EvaluatorCodeFits.case_zero
      (successorBranch :=
        .cons Code.one
          (.cons Code.head
            (Code.flatStripMotifStepCode.comp Code.tail)))
      (values := 0 :: Code.flatStripMotifState width period valid [])
      (by rfl)
      (zero'_named (Code.flatStripMotifState width period valid []))

def flatStripGuardLoopSpaceBound (inputSpace : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (inputSpace + 1)

private theorem flatStripGuardUpdatedCost_le
    (base : Nat) (positive : 1 ≤ base) :
    1000 *
        (500000000000000000000000000000000000000000000 * base + 1) ≤
      1000000000000000000000000000000000000000000000000 * base := by
  omega

set_option maxHeartbeats 1500000 in
theorem flatStripGuardBodyCost_le_input
    (periodicStrip : PeriodicStrip)
    (valid : Bool) (cell : Cell) (remaining leading : List Cell)
    (decomposition :
      periodicStrip.motif = leading ++ cell :: remaining) :
    flatStripGuardBodyCost (remaining.length + 1)
        periodicStrip.width periodicStrip.period valid cell remaining ≤
      flatStripGuardLoopSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip)) := by
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
  change flatStripGuardBodyCost (remaining.length + 1)
      periodicStrip.width periodicStrip.period valid cell remaining ≤
    flatStripGuardLoopSpaceBound inputSpace
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
  have widthSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have motifLengthSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.motif.length fields lengthMember
  have xSpace := guardEncodedFieldSpace_le_of_mem xCode fields xMember
  have ySpace := guardEncodedFieldSpace_le_of_mem yCode fields yMember
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
    change encodedListSpace fields = _
    rw [fieldsEq]
    simp [LeanTrominoes.FiniteState.encodedListSpace_append,
      PeriodicStripFlatEncoding.cellFields, xCode, yCode]
  have restSpace : encodedListSpace restFields ≤ inputSpace := by
    have suffix := guardEncodedListSpace_suffix_le
      ([periodicStrip.width, periodicStrip.period,
          periodicStrip.motif.length] ++
        leading.flatMap PeriodicStripFlatEncoding.cellFields ++
        PeriodicStripFlatEncoding.cellFields cell)
      restFields
    change encodedListSpace restFields ≤ encodedListSpace fields
    rw [fieldsEq]
    simpa [List.append_assoc] using suffix
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
  have withCellBits := encodeNat_add_length_le_sum
    (periodicStrip.width + periodicStrip.period) cellCode
  have doubledBits := encodeNat_mul_length_le_sum 2
    (periodicStrip.width + periodicStrip.period + cellCode)
  have localBits := encodeNat_add_length_le_sum
    (2 * (periodicStrip.width + periodicStrip.period + cellCode)) 4
  have twoBits : (Computability.encodeNat 2).length = 2 := rfl
  have fourBits : (Computability.encodeNat 4).length = 3 := rfl
  have cellPredicate := stripCellInBoundsCost_le_linear
    periodicStrip.width periodicStrip.period cell
  have cellPredicateInput :
      stripCellInBoundsCost periodicStrip.width periodicStrip.period cell ≤
        10000000000000 * (inputSpace + 1) := by
    change stripCellInBoundsCost periodicStrip.width periodicStrip.period cell ≤
      100000000000 *
        (encodedListSpace
          [2 * (periodicStrip.width + periodicStrip.period + cellCode) + 4] + 1)
      at cellPredicate
    rw [cellCodeEq] at cellPredicate withCellBits doubledBits localBits
    simp only [encodedListSpace_cons, encodedListSpace_nil] at cellPredicate
    omega
  have stateSpace : encodedListSpace state ≤ inputSpace + 2 := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    change encodedListSpace
      ([valid.toNat, periodicStrip.width, periodicStrip.period,
        xCode, yCode] ++ restFields) ≤ _
    cases valid <;>
      simp [LeanTrominoes.FiniteState.encodedListSpace_append,
        encodedListSpace_cons, zeroBits, oneBits] at inputExpanded ⊢ <;>
      omega
  let base := inputSpace + 1
  have get0Raw := listCodeGetCost_le_linear 0 state
  have get1Raw := listCodeGetCost_le_linear 1 state
  have get2Raw := listCodeGetCost_le_linear 2 state
  have get3Raw := listCodeGetCost_le_linear 3 state
  have get4Raw := listCodeGetCost_le_linear 4 state
  have drop5Raw := StripSavitchStep.dropCost_le_linear 5 state
  have get0Bound : getCost 0 state ≤ 1000000 * base := by omega
  have get1Bound : getCost 1 state ≤ 1000000 * base := by omega
  have get2Bound : getCost 2 state ≤ 1000000 * base := by omega
  have get3Bound : getCost 3 state ≤ 1000000 * base := by omega
  have get4Bound : getCost 4 state ≤ 1000000 * base := by omega
  have drop5Bound : dropCost 5 state ≤ 1000000 * base := by omega
  have xSingleton : encodedListSpace [xCode] ≤ base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ⊢
    simp only [base, inputSpace]
    omega
  have ySingleton : encodedListSpace [yCode] ≤ base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at ySpace ⊢
    simp only [base, inputSpace]
    omega
  have cellSingleton : encodedListSpace [cellCode] ≤ 3 * base := by
    simp only [cellCodeEq, encodedListSpace_cons, encodedListSpace_nil]
    omega
  have periodSingleton :
      encodedListSpace [periodicStrip.period] ≤ base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at periodSpace ⊢
    simp only [base, inputSpace]
    omega
  have widthSingleton :
      encodedListSpace [periodicStrip.width] ≤ base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at widthSpace ⊢
    simp only [base, inputSpace]
    omega
  have periodCellSpace :
      encodedListSpace [periodicStrip.period, cellCode] ≤ 4 * base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have cellArgumentsSpace : encodedListSpace
      [periodicStrip.width, periodicStrip.period, cellCode] ≤
        5 * base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have periodRestSpace : encodedListSpace
      (periodicStrip.period :: restFields) ≤ 2 * base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have dimensionsRestSpace : encodedListSpace
      (periodicStrip.width :: periodicStrip.period :: restFields) ≤
        3 * base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  have pairArgumentsSpace : encodedListSpace [xCode, yCode] ≤
      2 * base := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at *
    omega
  let pairArgumentsCost := prependCost state [xCode] [yCode]
    (getCost 3 state) (getCost 4 state)
  have pairArgumentsCostBound : pairArgumentsCost ≤ 10000000 * base := by
    simp only [pairArgumentsCost, prependCost, List.headI_cons]
    omega
  let cellCost := natPairCost xCode yCode + pairArgumentsCost
  have cellCostBound :
      cellCost ≤
        200000000000000000000000000000000000000000000 * base := by
    simp only [cellCost]
    omega
  let periodAndCellCost := prependCost state
    [periodicStrip.period] [cellCode] (getCost 2 state) cellCost
  have periodAndCellCostBound :
      periodAndCellCost ≤
        300000000000000000000000000000000000000000000 * base := by
    simp only [periodAndCellCost, prependCost, List.headI_cons]
    omega
  let cellArgumentsCost := prependCost state [periodicStrip.width]
    [periodicStrip.period, cellCode] (getCost 1 state) periodAndCellCost
  have cellArgumentsCostBound :
      cellArgumentsCost ≤
        400000000000000000000000000000000000000000000 * base := by
    simp only [cellArgumentsCost, prependCost, List.headI_cons]
    omega
  let inBoundsCost :=
    stripCellInBoundsCost periodicStrip.width periodicStrip.period cell +
      cellArgumentsCost
  have inBoundsCostBound :
      inBoundsCost ≤
        500000000000000000000000000000000000000000000 * base := by
    simp only [inBoundsCost]
    omega
  let cellTag :=
    if cell.InStripBounds periodicStrip.width periodicStrip.period then 1 else 0
  let boolBudget :=
    500000000000000000000000000000000000000000000 * base
  have boolBudgetPositive : 1 ≤ boolBudget := by
    simp only [boolBudget, base]
    omega
  have stateBoolBound : encodedListSpace state ≤ boolBudget := by
    simp only [boolBudget, base]
    omega
  have updatedRaw := flatLookupBoolAndCost_le_budget state valid.toNat
    cellTag (getCost 0 state) inBoundsCost boolBudget
    (by cases valid <;> simp) (by
      simp only [cellTag]
      split <;> omega) stateBoolBound (by
      simp only [boolBudget]
      omega) (by
      simp only [boolBudget]
      omega) boolBudgetPositive
  let updatedValidCost := boolAndCost state valid.toNat cellTag
    (getCost 0 state) inBoundsCost
  have updatedValidCostBound :
      updatedValidCost ≤
        1000000000000000000000000000000000000000000000000 * base := by
    change boolAndCost state valid.toNat cellTag
      (getCost 0 state) inBoundsCost ≤ _
    have raw := updatedRaw
    simp only [boolBudget] at raw
    exact raw.trans (flatStripGuardUpdatedCost_le base (by
      simp only [base]
      omega))
  let periodAndRestCost := prependCost state [periodicStrip.period]
    restFields (getCost 2 state) (dropCost 5 state)
  have periodAndRestCostBound :
      periodAndRestCost ≤ 10000000 * base := by
    simp only [periodAndRestCost, prependCost, List.headI_cons]
    omega
  let dimensionsAndRestCost := prependCost state [periodicStrip.width]
    (periodicStrip.period :: restFields) (getCost 1 state)
    periodAndRestCost
  have dimensionsAndRestCostBound :
      dimensionsAndRestCost ≤ 100000000 * base := by
    simp only [dimensionsAndRestCost, prependCost, List.headI_cons]
    omega
  let nextValid := valid &&
    decide (cell.InStripBounds periodicStrip.width periodicStrip.period)
  let nextState := Code.flatStripMotifState periodicStrip.width
    periodicStrip.period nextValid remaining
  have nextStateSpace : encodedListSpace nextState ≤ inputSpace + 2 := by
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    have oneBits : (Computability.encodeNat 1).length = 1 := rfl
    change encodedListSpace
      ([nextValid.toNat, periodicStrip.width, periodicStrip.period] ++
        restFields) ≤ _
    cases nextValid <;>
      simp [LeanTrominoes.FiniteState.encodedListSpace_append,
        encodedListSpace_cons, zeroBits, oneBits] at inputExpanded ⊢ <;>
      omega
  have nextValidSpace : encodedListSpace [nextValid.toNat] ≤ 2 := by
    cases nextValid <;> decide
  have finalOutputSpace : encodedListSpace
      (nextValid.toNat :: periodicStrip.width :: periodicStrip.period ::
        restFields) ≤ inputSpace + 2 := by
    change encodedListSpace nextState ≤ inputSpace + 2
    exact nextStateSpace
  have stepCostBound :
      flatStripGuardStepCost periodicStrip.width periodicStrip.period
          valid cell remaining ≤
        2000000000000000000000000000000000000000000000000 * base := by
    change prependCost state [nextValid.toNat]
      (periodicStrip.width :: periodicStrip.period :: restFields)
      updatedValidCost dimensionsAndRestCost ≤ _
    simp only [prependCost, List.headI_cons]
    omega
  let countdownBudget :=
    3000000000000000000000000000000000000000000000000 * base
  have remainingBits := listCodeEncodeNat_length_mono
    (show remaining.length ≤ remaining.length + 1 by omega)
  have predecessorInput : encodedListSpace
      (remaining.length :: state) ≤ countdownBudget := by
    simp only [countdownBudget, base, encodedListSpace_cons]
    omega
  have successorInput : encodedListSpace
      ((remaining.length + 1) :: state) ≤ countdownBudget := by
    simp only [countdownBudget, base, encodedListSpace_cons]
    omega
  have remainingSingleton : encodedListSpace [remaining.length] ≤
      countdownBudget := by
    simp only [countdownBudget, base, encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  have payloadOutput : encodedListSpace
      (remaining.length :: nextState) ≤ countdownBudget := by
    simp only [countdownBudget, base, encodedListSpace_cons]
    omega
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have taggedOutput : encodedListSpace
      (1 :: remaining.length :: nextState) ≤ countdownBudget := by
    simp only [countdownBudget, base, encodedListSpace_cons, oneBits]
    omega
  have bodyBound := flatLookupCountdownBodySuccCost_le_budget
    remaining.length state nextState
    (flatStripGuardStepCost periodicStrip.width periodicStrip.period
      valid cell remaining) countdownBudget successorInput predecessorInput
    remainingSingleton payloadOutput taggedOutput (by
      simp only [countdownBudget]
      omega)
  apply bodyBound.trans
  simp only [flatStripGuardLoopSpaceBound, countdownBudget, base, inputSpace]
  omega

theorem flatStripGuardBodyZeroCost_le_input
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    flatStripGuardBodyZeroCost periodicStrip.width
        periodicStrip.period valid ≤
      flatStripGuardLoopSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip)) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputSpace := encodedListSpace fields
  have widthMember : periodicStrip.width ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have periodMember : periodicStrip.period ∈ fields := by
    simp [fields, PeriodicStripFlatEncoding.stripFields]
  have widthSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  cases valid <;>
    simp [flatStripGuardBodyZeroCost, flatCountdownBodyCost,
      zeroPrimeCost, Code.flatStripMotifState,
      encodedListSpace_cons, encodedListSpace_nil,
      flatStripGuardLoopSpaceBound,
      fields, inputSpace, zeroBits, oneBits] at * <;>
    omega

/-! ## Uniform reachable-state guard loop -/

/-- Reachable states of the native flat guard retain an exact typed suffix of
the original motif, synchronized with the countdown. -/
def FlatStripGuardReachable (periodicStrip : PeriodicStrip)
    (remaining : Nat) (values : List Nat) : Prop :=
  ∃ valid motif leading,
    values = Code.flatStripMotifState periodicStrip.width
      periodicStrip.period valid motif ∧
    remaining = motif.length ∧
    periodicStrip.motif = leading ++ motif

theorem flatStripGuardReachable_initial
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    FlatStripGuardReachable periodicStrip periodicStrip.motif.length
      (Code.flatStripMotifState periodicStrip.width
        periodicStrip.period valid periodicStrip.motif) := by
  exact ⟨valid, periodicStrip.motif, [], rfl, rfl, by simp⟩

theorem flatStripGuardReachable_preserved
    (periodicStrip : PeriodicStrip)
    (remaining : Nat) (values : List Nat)
    (reachable :
      FlatStripGuardReachable periodicStrip (remaining + 1) values) :
    FlatStripGuardReachable periodicStrip remaining
      (Code.flatStripMotifNativeStep values) := by
  obtain ⟨valid, motif, leading, rfl, remainingEq, suffix⟩ := reachable
  cases motif with
  | nil => simp at remainingEq
  | cons cell motif =>
      have remainingEq' : remaining = motif.length := by
        simpa using Nat.succ.inj remainingEq
      subst remaining
      refine ⟨valid && decide
          (cell.InStripBounds periodicStrip.width periodicStrip.period),
        motif, leading ++ [cell], ?_, rfl, ?_⟩
      · exact Code.flatStripMotifNativeStep_state_cons
          periodicStrip.width periodicStrip.period valid cell motif
      · simpa [List.append_assoc] using suffix

theorem flatStripGuardReachableBody_fits
    (periodicStrip : PeriodicStrip)
    (remaining : Nat) (values : List Nat)
    (reachable : FlatStripGuardReachable periodicStrip remaining values) :
    EvaluatorCodeFits
      (Code.flatCountdownBody Code.flatStripMotifStepCode)
      (remaining :: values)
      (flatCountdownOutput Code.flatStripMotifNativeStep remaining values)
      (flatStripGuardLoopSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip))) := by
  obtain ⟨valid, motif, leading, rfl, remainingEq, suffix⟩ := reachable
  cases motif with
  | nil =>
      simp only [List.length_nil] at remainingEq
      subst remaining
      simpa [flatCountdownOutput] using
        (flatStripGuardBodyZero_fits periodicStrip.width
          periodicStrip.period valid).mono
          (flatStripGuardBodyZeroCost_le_input periodicStrip valid)
  | cons cell motif =>
      have remainingEq' : remaining = motif.length + 1 := by
        simpa using remainingEq
      subst remaining
      simpa [flatCountdownOutput,
        Code.flatStripMotifNativeStep_state_cons] using
        (flatStripGuardBodySucc_fits motif.length periodicStrip.width
          periodicStrip.period valid cell motif).mono
          (flatStripGuardBodyCost_le_input periodicStrip valid cell motif
            leading suffix)

/-- The full native guard scan reuses one input-linear body reserve throughout
the tail-recursive countdown. -/
theorem flatStripGuardLoop_fits
    (periodicStrip : PeriodicStrip) (valid : Bool) :
    EvaluatorCodeFits
      (Code.flatIterate Code.flatStripMotifStepCode)
      (periodicStrip.motif.length ::
        Code.flatStripMotifState periodicStrip.width
          periodicStrip.period valid periodicStrip.motif)
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        (valid && motifInStripBounds periodicStrip.width
          periodicStrip.period periodicStrip.motif) [])
      (flatStripGuardLoopSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip))) where
  input_space :=
    (flatStripGuardReachableBody_fits periodicStrip
      periodicStrip.motif.length
      (Code.flatStripMotifState periodicStrip.width
        periodicStrip.period valid periodicStrip.motif)
      (flatStripGuardReachable_initial periodicStrip valid)).input_space
  output_space := by
    let result := valid && motifInStripBounds periodicStrip.width
      periodicStrip.period periodicStrip.motif
    have zeroFit :=
      (flatStripGuardBodyZero_fits periodicStrip.width
        periodicStrip.period result).mono
        (flatStripGuardBodyZeroCost_le_input periodicStrip result)
    have tailSpace := listCodeEncodedListSpace_tail_le
      (0 :: Code.flatStripMotifState periodicStrip.width
        periodicStrip.period result [])
    simp only [List.tail_cons] at tailSpace
    exact tailSpace.trans zeroFit.input_space
  call continuation bound budget after := by
    apply EvaluatorCallFits.flatIterate_of_reachable_code_fits
      (step := Code.flatStripMotifNativeStep)
      (bodyCost := fun _ _ => flatStripGuardLoopSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip)))
      (invariant := FlatStripGuardReachable periodicStrip)
    · exact flatStripGuardReachableBody_fits periodicStrip
    · exact flatStripGuardReachable_initial periodicStrip valid
    · exact flatStripGuardReachable_preserved periodicStrip
    · intro remaining values reachable
      exact budget
    · rw [Code.flatStripMotifNativeStep_iterate]
      exact after

/-! ## Complete well-formedness guard -/

def flatStripGuardDimensionWidthCost
    (periodicStrip : PeriodicStrip) : Nat :=
  natPositiveCost periodicStrip.width +
    getCost 0 (PeriodicStripFlatEncoding.stripFields periodicStrip)

theorem flatStripGuardDimensionWidth_fits
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 0))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.width)).toNat]
      (flatStripGuardDimensionWidthCost periodicStrip) := by
  by_cases positive : 0 < periodicStrip.width <;>
    simpa [flatStripGuardDimensionWidthCost, positive,
      PeriodicStripFlatEncoding.stripFields] using
      EvaluatorCodeFits.comp (natPositive periodicStrip.width)
        (get 0 (PeriodicStripFlatEncoding.stripFields periodicStrip))

def flatStripGuardDimensionPeriodCost
    (periodicStrip : PeriodicStrip) : Nat :=
  natPositiveCost periodicStrip.period +
    getCost 1 (PeriodicStripFlatEncoding.stripFields periodicStrip)

theorem flatStripGuardDimensionPeriod_fits
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.natPositiveCode.comp (Code.get 1))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.period)).toNat]
      (flatStripGuardDimensionPeriodCost periodicStrip) := by
  by_cases positive : 0 < periodicStrip.period <;>
    simpa [flatStripGuardDimensionPeriodCost, positive,
      PeriodicStripFlatEncoding.stripFields] using
      EvaluatorCodeFits.comp (natPositive periodicStrip.period)
        (get 1 (PeriodicStripFlatEncoding.stripFields periodicStrip))

def flatStripGuardDimensionsValidCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  boolAndCost fields
    (decide (0 < periodicStrip.width)).toNat
    (decide (0 < periodicStrip.period)).toNat
    (flatStripGuardDimensionWidthCost periodicStrip)
    (flatStripGuardDimensionPeriodCost periodicStrip)

theorem flatStripGuardDimensionsValid_fits
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.stripDimensionsValidCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (0 < periodicStrip.width) &&
        decide (0 < periodicStrip.period)).toNat]
      (flatStripGuardDimensionsValidCost periodicStrip) := by
  have fitted := boolAnd
    (flatStripGuardDimensionWidth_fits periodicStrip)
    (flatStripGuardDimensionPeriod_fits periodicStrip)
  by_cases widthPositive : 0 < periodicStrip.width <;>
    by_cases periodPositive : 0 < periodicStrip.period <;>
    simpa [Code.stripDimensionsValidCode,
      flatStripGuardDimensionsValidCost,
      widthPositive, periodPositive] using fitted

def flatStripGuardPeriodAndCoordinatesCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let coordinates :=
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [periodicStrip.period] coordinates
    (getCost 1 fields) (dropCost 3 fields)

theorem flatStripGuardPeriodAndCoordinates_fits
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.period ::
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripGuardPeriodAndCoordinatesCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  simpa [flatStripGuardPeriodAndCoordinatesCost, fields, prependCost,
    PeriodicStripFlatEncoding.stripFields] using
    prepend (get 1 fields) (drop 3 fields)

def flatStripGuardDimensionsAndCoordinatesCost
    (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let rest := periodicStrip.period ::
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [periodicStrip.width] rest
    (getCost 0 fields)
    (flatStripGuardPeriodAndCoordinatesCost periodicStrip)

theorem flatStripGuardDimensionsAndCoordinates_fits
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 0) <|
        Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.width :: periodicStrip.period ::
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatStripGuardDimensionsAndCoordinatesCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  simpa [flatStripGuardDimensionsAndCoordinatesCost, fields, prependCost,
    PeriodicStripFlatEncoding.stripFields] using
    prepend (get 0 fields)
      (flatStripGuardPeriodAndCoordinates_fits periodicStrip)

def flatStripGuardPayloadCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let rest := periodicStrip.width :: periodicStrip.period ::
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields
  prependCost fields [dimensionsValid.toNat] rest
    (flatStripGuardDimensionsValidCost periodicStrip)
    (flatStripGuardDimensionsAndCoordinatesCost periodicStrip)

theorem flatStripGuardPayload_fits (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
    EvaluatorCodeFits
      (Code.prepend Code.stripDimensionsValidCode <|
        Code.prepend (Code.get 0) <|
          Code.prepend (Code.get 1) (Code.drop 3))
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        dimensionsValid periodicStrip.motif)
      (flatStripGuardPayloadCost periodicStrip) := by
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  simpa [flatStripGuardPayloadCost, dimensionsValid, prependCost,
    Code.flatStripMotifState] using
    prepend (flatStripGuardDimensionsValid_fits periodicStrip)
      (flatStripGuardDimensionsAndCoordinates_fits periodicStrip)

def flatStripGuardLoopInputCost (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let payload := Code.flatStripMotifState periodicStrip.width
    periodicStrip.period dimensionsValid periodicStrip.motif
  prependCost fields [periodicStrip.motif.length] payload
    (getCost 2 fields) (flatStripGuardPayloadCost periodicStrip)

theorem flatStripGuardLoopInput_fits (periodicStrip : PeriodicStrip) :
    let dimensionsValid :=
      decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
    EvaluatorCodeFits Code.flatStripWellFormedLoopInputCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (periodicStrip.motif.length ::
        Code.flatStripMotifState periodicStrip.width periodicStrip.period
          dimensionsValid periodicStrip.motif)
      (flatStripGuardLoopInputCost periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  simpa [Code.flatStripWellFormedLoopInputCode,
    flatStripGuardLoopInputCost, fields, dimensionsValid,
    prependCost, PeriodicStripFlatEncoding.stripFields] using
    prepend (get 2 fields) (flatStripGuardPayload_fits periodicStrip)

set_option maxHeartbeats 1000000 in
theorem flatStripGuardLoopInputCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripGuardLoopInputCost periodicStrip ≤
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
      PeriodicStripFlatEncoding.stripFields, encodedListSpace_cons]
  have widthSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.width
  have periodSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.period
  have lengthSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.motif.length
  have widthPredBits := listCodeEncodeNat_length_mono
    (Nat.sub_le periodicStrip.width 1)
  have periodPredBits := listCodeEncodeNat_length_mono
    (Nat.sub_le periodicStrip.period 1)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have widthZeroIff : periodicStrip.width = 0 ↔
      ¬ 0 < periodicStrip.width := by omega
  have periodZeroIff : periodicStrip.period = 0 ↔
      ¬ 0 < periodicStrip.period := by omega
  by_cases widthPositive : 0 < periodicStrip.width <;>
    by_cases periodPositive : 0 < periodicStrip.period <;>
    simp [flatStripGuardLoopInputCost, flatStripGuardPayloadCost,
      flatStripGuardDimensionsAndCoordinatesCost,
      flatStripGuardPeriodAndCoordinatesCost,
      flatStripGuardDimensionsValidCost,
      flatStripGuardDimensionWidthCost,
      flatStripGuardDimensionPeriodCost, natPositiveCost,
      boolAndCost, normalizeBoolCost, prependCost,
      branchZeroZeroCost, branchZeroSuccCost, branchZeroTestCost,
      getCost, dropCost, idCost, headCost, nilCost, oneCost,
      zeroCost, zeroPrimeCost, tailCost, succCost,
      Code.flatStripMotifState, PeriodicStripFlatEncoding.cellFields,
      PeriodicStripFlatEncoding.stripFields,
      fields, coordinates, inputSpace, inputExpanded,
      widthPositive, periodPositive, widthZeroIff, periodZeroIff,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits] at * <;>
    omega

theorem flatStripGuardProjectionCost_le_input
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
  have widthSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.width fields widthMember
  have periodSpace := guardEncodedFieldSpace_le_of_mem
    periodicStrip.period fields periodMember
  have widthSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.width
  have periodSuccBits :=
    listCodeEncodeNat_succ_length_le periodicStrip.period
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  have twoBits : (Computability.encodeNat 2).length = 2 := rfl
  cases result <;>
    simp [getCost, dropCost, idCost, headCost, nilCost,
      zeroPrimeCost, tailCost, succCost,
      Code.flatStripMotifState, fields, inputSpace,
      encodedListSpace_cons, encodedListSpace_nil,
      zeroBits, oneBits, twoBits] at * <;>
    omega

def flatStripWellFormedSpaceBound (inputSpace : Nat) : Nat :=
  3 * flatStripGuardLoopSpaceBound inputSpace

/-- Complete native flat well-formedness validation, including preparation and
result projection, in a linear reserve over the original flat fields. -/
theorem flatStripWellFormed_fits (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.flatStripWellFormedCode
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [periodicStrip.wellFormed.toNat]
      (flatStripWellFormedSpaceBound
        (encodedListSpace
          (PeriodicStripFlatEncoding.stripFields periodicStrip))) := by
  let inputSpace := encodedListSpace
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
  let dimensionsValid :=
    decide (0 < periodicStrip.width) && decide (0 < periodicStrip.period)
  let result := dimensionsValid &&
    motifInStripBounds periodicStrip.width periodicStrip.period
      periodicStrip.motif
  let loopBound := flatStripGuardLoopSpaceBound inputSpace
  have preparedBound : flatStripGuardLoopInputCost periodicStrip ≤
      loopBound := by
    have prepared := flatStripGuardLoopInputCost_le_input periodicStrip
    simp only [loopBound, flatStripGuardLoopSpaceBound, inputSpace]
    omega
  have projectionBound : getCost 0
      (Code.flatStripMotifState periodicStrip.width periodicStrip.period
        result []) ≤ loopBound := by
    have projected := flatStripGuardProjectionCost_le_input
      periodicStrip result
    simp only [loopBound, flatStripGuardLoopSpaceBound, inputSpace]
    omega
  have prepared := EvaluatorCodeFits.comp
    (flatStripGuardLoop_fits periodicStrip dimensionsValid)
    (flatStripGuardLoopInput_fits periodicStrip)
  have preparedUniform := prepared.mono (show
      flatStripGuardLoopSpaceBound
            (encodedListSpace
              (PeriodicStripFlatEncoding.stripFields periodicStrip)) +
          flatStripGuardLoopInputCost periodicStrip ≤ 2 * loopBound by
    change loopBound + flatStripGuardLoopInputCost periodicStrip ≤
      2 * loopBound
    omega)
  have projected := EvaluatorCodeFits.comp
    (get 0 (Code.flatStripMotifState periodicStrip.width
      periodicStrip.period result [])) preparedUniform
  have final := projected.mono (show
      getCost 0
            (Code.flatStripMotifState periodicStrip.width
              periodicStrip.period result []) +
          2 * loopBound ≤ flatStripWellFormedSpaceBound inputSpace by
    change getCost 0
          (Code.flatStripMotifState periodicStrip.width
            periodicStrip.period result []) +
        2 * loopBound ≤ 3 * loopBound
    omega)
  simpa [Code.flatStripWellFormedCode, dimensionsValid, result,
    inputSpace, Code.stripWellFormedAccumulator_eq,
    Code.flatStripMotifState] using final

/-! ## Guarded cycle-search composition -/

def flatStripCycleBranchCost (periodicStrip : PeriodicStrip) : Nat :=
  FlatStripCyclePartrec.flatStripCycleSearchSpaceBound
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
    flatStripCycleParametersCost periodicStrip

theorem flatStripCycleBranch_fits (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    EvaluatorCodeFits
      ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
        flatStripCycleParametersCode)
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [divideBoolTag
        (cycleSearchIndexDFSBoolAtDepth
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip))]
      (flatStripCycleBranchCost periodicStrip) := by
  simpa [flatStripCycleBranchCost] using EvaluatorCodeFits.comp
    (FlatStripCyclePartrec.flatStripCycleSearch_fits_polynomial
      tromino periodicStrip wellFormed)
    (flatStripCycleParameters_fits periodicStrip)

private theorem flatEncodeBool_eq_divideBoolTag (value : Bool) :
    Encodable.encode value = divideBoolTag value := by
  cases value <;> rfl

def flatPeriodicStripTrominoTilingCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Nat :=
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let output := [Encodable.encode
    (flatPeriodicStripTrominoTilingBool tromino periodicStrip)]
  if _wellFormed : periodicStrip.IsWellFormed then
    branchZeroSuccCost fields output periodicStrip.wellFormed.toNat
      (flatStripWellFormedSpaceBound (encodedListSpace fields))
      (flatStripCycleBranchCost periodicStrip)
  else
    branchZeroZeroCost fields output periodicStrip.wellFormed.toNat
      (flatStripWellFormedSpaceBound (encodedListSpace fields))
      (zeroCost fields)

set_option maxHeartbeats 1000000 in
/-- Exact evaluator certificate for the complete native-flat guarded
cycle-search decider. -/
theorem flatPeriodicStripTrominoTiling_fits
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits (flatPeriodicStripTrominoTilingCode tromino)
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [Encodable.encode
        (flatPeriodicStripTrominoTilingBool tromino periodicStrip)]
      (flatPeriodicStripTrominoTilingCost tromino periodicStrip) := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  by_cases wellFormed : periodicStrip.IsWellFormed
  · have wellFormedBool : periodicStrip.wellFormed = true :=
      (periodicStrip.wellFormed_eq_true_iff).mpr wellFormed
    let result := cycleSearchIndexDFSBoolAtDepth
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip)
      (indexedTransitionRawBool tromino periodicStrip)
    have selected := branchZero_succ
      (whenZero := Code.zero)
      (testValue := periodicStrip.wellFormed.toNat)
      (show 0 < periodicStrip.wellFormed.toNat by
        simp [wellFormedBool])
      (flatStripWellFormed_fits periodicStrip)
      (flatStripCycleBranch_fits tromino periodicStrip wellFormed)
    have resultEq :
        flatPeriodicStripTrominoTilingBool tromino periodicStrip =
          result := by
      simp [flatPeriodicStripTrominoTilingBool, wellFormed, result]
      rfl
    have costEq :
        flatPeriodicStripTrominoTilingCost tromino periodicStrip =
          branchZeroSuccCost fields [divideBoolTag result]
            periodicStrip.wellFormed.toNat
            (flatStripWellFormedSpaceBound (encodedListSpace fields))
            (flatStripCycleBranchCost periodicStrip) := by
      simp only [flatPeriodicStripTrominoTilingCost, fields,
        dif_pos wellFormed, resultEq, flatEncodeBool_eq_divideBoolTag]
    rw [resultEq]
    rw [flatEncodeBool_eq_divideBoolTag]
    rw [costEq]
    change EvaluatorCodeFits
      (Code.branchZero Code.flatStripWellFormedCode Code.zero
        ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
          flatStripCycleParametersCode))
      fields [divideBoolTag result]
      (branchZeroSuccCost fields [divideBoolTag result]
        periodicStrip.wellFormed.toNat
        (flatStripWellFormedSpaceBound (encodedListSpace fields))
        (flatStripCycleBranchCost periodicStrip))
    exact selected
  · have wellFormedBool : periodicStrip.wellFormed = false := by
      apply Bool.eq_false_iff.mpr
      intro true
      exact wellFormed
        ((periodicStrip.wellFormed_eq_true_iff).mp true)
    have selected := branchZero_zero
      (whenSucc :=
        (FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
          flatStripCycleParametersCode)
      (testValue := periodicStrip.wellFormed.toNat)
      (show periodicStrip.wellFormed.toNat = 0 by
        simp [wellFormedBool])
      (flatStripWellFormed_fits periodicStrip)
      (zero fields)
    have resultEq :
        flatPeriodicStripTrominoTilingBool tromino periodicStrip =
          false := by
      simp [flatPeriodicStripTrominoTilingBool, wellFormed]
    have costEq :
        flatPeriodicStripTrominoTilingCost tromino periodicStrip =
          branchZeroZeroCost fields [divideBoolTag false]
            periodicStrip.wellFormed.toNat
            (flatStripWellFormedSpaceBound (encodedListSpace fields))
            (zeroCost fields) := by
      simp only [flatPeriodicStripTrominoTilingCost, fields,
        dif_neg wellFormed, resultEq, flatEncodeBool_eq_divideBoolTag]
    rw [resultEq, flatEncodeBool_eq_divideBoolTag]
    rw [costEq]
    change EvaluatorCodeFits
      (Code.branchZero Code.flatStripWellFormedCode Code.zero
        ((FlatStripCyclePartrec.flatStripCycleSearchCode tromino).comp
          flatStripCycleParametersCode))
      fields [divideBoolTag false]
      (branchZeroZeroCost fields [divideBoolTag false]
        periodicStrip.wellFormed.toNat
        (flatStripWellFormedSpaceBound (encodedListSpace fields))
        (zeroCost fields))
    exact selected

/-! ## Polynomial form of the cycle-search reserve -/

set_option maxRecDepth 10000

noncomputable def flatStripReachStateSpacePolynomial : Polynomial Nat :=
  stripDFSPartrecSpacePolynomial + 43 * Polynomial.X + 10

@[simp] theorem flatStripReachStateSpacePolynomial_eval (inputLength : Nat) :
    flatStripReachStateSpacePolynomial.eval inputLength =
      flatStripReachStateSpaceBound inputLength := by
  simp [flatStripReachStateSpacePolynomial,
    flatStripReachStateSpaceBound]

noncomputable def flatStripFuelBitsPolynomial : Polynomial Nat :=
  (21 * Polynomial.X + 2) * (21 * Polynomial.X + 5) + 1

@[simp] theorem flatStripFuelBitsPolynomial_eval (inputLength : Nat) :
    flatStripFuelBitsPolynomial.eval inputLength =
      flatStripFuelBits inputLength := by
  simp [flatStripFuelBitsPolynomial, flatStripFuelBits]

noncomputable def flatStripReachPayloadSpacePolynomial : Polynomial Nat :=
  flatStripReachStateSpacePolynomial + flatStripFuelBitsPolynomial + 2

@[simp] theorem flatStripReachPayloadSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripReachPayloadSpacePolynomial.eval inputLength =
      flatStripReachPayloadSpaceBound inputLength := by
  simp [flatStripReachPayloadSpacePolynomial,
    flatStripReachPayloadSpaceBound]

noncomputable def flatStripLeafSpacePolynomial : Polynomial Nat :=
  flatStripReachStateSpacePolynomial + 100 * Polynomial.X + 120

@[simp] theorem flatStripLeafSpacePolynomial_eval (inputLength : Nat) :
    flatStripLeafSpacePolynomial.eval inputLength =
      flatStripLeafSpaceUnit inputLength := by
  simp [flatStripLeafSpacePolynomial, flatStripLeafSpaceUnit]

noncomputable def flatStripContextUniformSpacePolynomial : Polynomial Nat :=
  1000000000000000000000000000000000000000000000000000000000000000 *
      flatStripLeafSpacePolynomial +
    1000000000000000000000000000000 * flatStripLeafSpacePolynomial +
    1000000000 * flatStripLeafSpacePolynomial

@[simp] theorem flatStripContextUniformSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripContextUniformSpacePolynomial.eval inputLength =
      flatStripContextUniformSpaceBound inputLength := by
  simp [flatStripContextUniformSpacePolynomial,
    flatStripContextUniformSpaceBound]

noncomputable def flatStripPackedTransitionUnitPolynomial : Polynomial Nat :=
  8 * flatStripLeafSpacePolynomial + 10

@[simp] theorem flatStripPackedTransitionUnitPolynomial_eval
    (inputLength : Nat) :
    flatStripPackedTransitionUnitPolynomial.eval inputLength =
      flatStripPackedTransitionUnitBound inputLength := by
  simp [flatStripPackedTransitionUnitPolynomial,
    flatStripPackedTransitionUnitBound]

noncomputable def flatPackedTransitionEnvelopePolynomial
    (unit : Polynomial Nat) : Polynomial Nat :=
  let normalizationBody :=
    10000000000000000000000000000000000000000000000000000000000000000000000000000000000 *
      unit ^ 2
  let normalizationColumn :=
    200000 * (normalizationBody * unit + unit + 1)
  let normalizationLastTwo := 1000 * (normalizationColumn + 1)
  let normalizationLastThree := 1000 * (normalizationLastTwo + 1)
  let normalizationLastFour := 1000 * (normalizationLastThree + 1)
  let normalizationAll := 1000 * (normalizationLastFour + 1)
  let centerBody := (10 ^ 1100) * unit ^ 2
  let centerValid := 200000 * (centerBody * unit + unit + 1)
  let overlapBody := (10 ^ 1100) * unit ^ 2
  let overlapColumn := 200000 * (overlapBody * unit + unit + 1)
  let overlapLastTwo := 1000 * (overlapColumn + 1)
  let overlapLastThree := 1000 * (overlapLastTwo + 1)
  let overlapColumns := 1000 * (overlapLastThree + 1)
  let phase := 100000000000000000000000000000000 * unit
  let component :=
    normalizationAll + centerValid + overlapColumns + phase + unit + 1
  let overlap := 1000 * (component + 1)
  let tail := 1000 * (overlap + 1)
  1000 * (tail + 1)

@[simp] theorem flatPackedTransitionEnvelopePolynomial_eval
    (unit : Polynomial Nat) (inputLength : Nat) :
    (flatPackedTransitionEnvelopePolynomial unit).eval inputLength =
      flatPackedTransitionSpaceEnvelope (unit.eval inputLength) := by
  simp [flatPackedTransitionEnvelopePolynomial,
    flatPackedTransitionSpaceEnvelope]

noncomputable def flatStripPackedTransitionUniformSpacePolynomial :
    Polynomial Nat :=
  flatPackedTransitionEnvelopePolynomial
    flatStripPackedTransitionUnitPolynomial

@[simp] theorem flatStripPackedTransitionUniformSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripPackedTransitionUniformSpacePolynomial.eval inputLength =
      flatStripPackedTransitionUniformSpaceBound inputLength := by
  simp [flatStripPackedTransitionUniformSpacePolynomial,
    flatStripPackedTransitionUniformSpaceBound]

noncomputable def flatStripTransitionUniformSpacePolynomial : Polynomial Nat :=
  flatStripPackedTransitionUniformSpacePolynomial +
    100 * flatStripContextUniformSpacePolynomial

@[simp] theorem flatStripTransitionUniformSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripTransitionUniformSpacePolynomial.eval inputLength =
      flatStripTransitionUniformSpaceBound inputLength := by
  simp [flatStripTransitionUniformSpacePolynomial,
    flatStripTransitionUniformSpaceBound]

noncomputable def flatStripBaseUniformSpacePolynomial : Polynomial Nat :=
  let unit := flatStripLeafSpacePolynomial
  let context := flatStripContextUniformSpacePolynomial
  let equality := 10000000000 * unit + context
  let transition := flatStripPackedTransitionUniformSpacePolynomial +
    100 * context
  1000 *
    (equality + transition + flatStripReachStateSpacePolynomial + 12 + 1)

@[simp] theorem flatStripBaseUniformSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripBaseUniformSpacePolynomial.eval inputLength =
      flatStripBaseUniformSpaceBound inputLength := by
  simp [flatStripBaseUniformSpacePolynomial,
    flatStripBaseUniformSpaceBound]

noncomputable def flatStripSavitchStepSpacePolynomial : Polynomial Nat :=
  1000000000000000000000000000000 *
    (flatStripReachStateSpacePolynomial +
      flatStripBaseUniformSpacePolynomial + 1)

@[simp] theorem flatStripSavitchStepSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripSavitchStepSpacePolynomial.eval inputLength =
      flatStripSavitchStepSpaceBound inputLength := by
  simp [flatStripSavitchStepSpacePolynomial,
    flatStripSavitchStepSpaceBound]

noncomputable def flatStripSavitchBodySpacePolynomial : Polynomial Nat :=
  100000 * (flatStripSavitchStepSpacePolynomial +
    flatStripReachPayloadSpacePolynomial + 1)

@[simp] theorem flatStripSavitchBodySpacePolynomial_eval
    (inputLength : Nat) :
    flatStripSavitchBodySpacePolynomial.eval inputLength =
      flatStripSavitchBodySpaceBound inputLength := by
  simp [flatStripSavitchBodySpacePolynomial,
    flatStripSavitchBodySpaceBound]

noncomputable def flatStripReachQuerySpacePolynomial : Polynomial Nat :=
  100 * Polynomial.X + 100

@[simp] theorem flatStripReachQuerySpacePolynomial_eval
    (inputLength : Nat) :
    flatStripReachQuerySpacePolynomial.eval inputLength =
      flatStripReachQuerySpaceBound inputLength := by
  simp [flatStripReachQuerySpacePolynomial,
    flatStripReachQuerySpaceBound]

noncomputable def flatStripFuelComputationSpacePolynomial : Polynomial Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (flatStripFuelBitsPolynomial + 100 * Polynomial.X + 100)

@[simp] theorem flatStripFuelComputationSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripFuelComputationSpacePolynomial.eval inputLength =
      flatStripFuelComputationSpaceBound inputLength := by
  simp [flatStripFuelComputationSpacePolynomial,
    flatStripFuelComputationSpaceBound]

noncomputable def flatStripReachCallSpacePolynomial : Polynomial Nat :=
  1000000000 *
    (flatStripFuelComputationSpacePolynomial +
      flatStripReachQuerySpacePolynomial +
      flatStripReachPayloadSpacePolynomial +
      flatStripSavitchBodySpacePolynomial + 1)

@[simp] theorem flatStripReachCallSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripReachCallSpacePolynomial.eval inputLength =
      flatStripReachCallSpaceBound inputLength := by
  simp [flatStripReachCallSpacePolynomial,
    flatStripReachCallSpaceBound]

noncomputable def flatStripCycleListSpacePolynomial : Polynomial Nat :=
  100 * (flatStripReachQuerySpacePolynomial +
    flatStripReachStateSpacePolynomial + 1)

@[simp] theorem flatStripCycleListSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleListSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleListSpaceBound inputLength := by
  simp [flatStripCycleListSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleListSpaceBound]

noncomputable def flatStripCycleAdapterSpacePolynomial : Polynomial Nat :=
  1000000000 * (flatStripCycleListSpacePolynomial + 1)

@[simp] theorem flatStripCycleAdapterSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleAdapterSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleAdapterSpaceBound inputLength := by
  simp [flatStripCycleAdapterSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleAdapterSpaceBound]

noncomputable def flatStripCycleCandidateComponentPolynomial : Polynomial Nat :=
  flatStripTransitionUniformSpacePolynomial +
    flatStripReachCallSpacePolynomial +
    2 * flatStripCycleAdapterSpacePolynomial +
    flatStripCycleListSpacePolynomial + 10

@[simp] theorem flatStripCycleCandidateComponentPolynomial_eval
    (inputLength : Nat) :
    flatStripCycleCandidateComponentPolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleCandidateComponentBound
        inputLength := by
  simp [flatStripCycleCandidateComponentPolynomial,
    FlatStripCyclePartrec.flatStripCycleCandidateComponentBound]

noncomputable def flatStripCycleCandidateSpacePolynomial : Polynomial Nat :=
  1000000000000 * (flatStripCycleCandidateComponentPolynomial + 1)

@[simp] theorem flatStripCycleCandidateSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleCandidateSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleCandidateSpaceBound inputLength := by
  simp [flatStripCycleCandidateSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleCandidateSpaceBound]

noncomputable def flatStripCycleLoopSpacePolynomial : Polynomial Nat :=
  4 * (flatStripCycleListSpacePolynomial + 1)

@[simp] theorem flatStripCycleLoopSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleLoopSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleLoopSpaceBound inputLength := by
  simp [flatStripCycleLoopSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleLoopSpaceBound]

noncomputable def flatStripCycleCandidateBodySpacePolynomial : Polynomial Nat :=
  100000 * (flatStripCycleCandidateSpacePolynomial +
    flatStripCycleLoopSpacePolynomial + 1)

@[simp] theorem flatStripCycleCandidateBodySpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleCandidateBodySpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleCandidateBodySpaceBound
        inputLength := by
  simp [flatStripCycleCandidateBodySpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleCandidateBodySpaceBound]

noncomputable def flatStripCycleInnerScanSpacePolynomial : Polynomial Nat :=
  1000 * (flatStripCycleCandidateBodySpacePolynomial +
    2 * flatStripCycleAdapterSpacePolynomial + 1)

@[simp] theorem flatStripCycleInnerScanSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleInnerScanSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleInnerScanSpaceBound inputLength := by
  simp [flatStripCycleInnerScanSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleInnerScanSpaceBound]

noncomputable def flatStripCycleOuterBodySpacePolynomial : Polynomial Nat :=
  100000 * (flatStripCycleInnerScanSpacePolynomial +
    flatStripCycleLoopSpacePolynomial + 1)

@[simp] theorem flatStripCycleOuterBodySpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleOuterBodySpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleOuterBodySpaceBound inputLength := by
  simp [flatStripCycleOuterBodySpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleOuterBodySpaceBound]

noncomputable def flatStripCycleSearchSpacePolynomial : Polynomial Nat :=
  100000 * (flatStripCycleOuterBodySpacePolynomial +
    flatStripCycleAdapterSpacePolynomial +
    flatStripCycleListSpacePolynomial + 1)

@[simp] theorem flatStripCycleSearchSpacePolynomial_eval
    (inputLength : Nat) :
    flatStripCycleSearchSpacePolynomial.eval inputLength =
      FlatStripCyclePartrec.flatStripCycleSearchSpaceBound inputLength := by
  simp [flatStripCycleSearchSpacePolynomial,
    FlatStripCyclePartrec.flatStripCycleSearchSpaceBound]

/-! ## Polynomial bound for parameter preparation and guarding -/

def flatStripParameterComponentBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (inputLength + 1)

def flatStripParameterSpaceBound (inputLength : Nat) : Nat :=
  1000000000 * flatStripParameterComponentBound inputLength

set_option maxHeartbeats 1000000 in
theorem flatStripEncodedListSpaceInputCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripEncodedListSpaceInputCost
        (PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripParameterComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let motifLength := periodicStrip.motif.length
  have inputSpace : encodedListSpace fields = inputLength := by
    simp [fields, inputLength,
      PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
  have motifLengthBound :=
    PeriodicStripFlatEncoding.motif_length_le_encoding_length periodicStrip
  have get2 := listCodeGetCost_le_linear 2 fields
  have zero := listCodeZeroCost_le_linear fields
  have identity := StripSavitchStep.idCost_le_linear fields
  have addition := natAddCost_le_linear motifLength motifLength
  have addConstant := addConstCost_le 3 [motifLength + motifLength]
  have motifBits := encodeNat_length_le_self motifLength
  have doubledBits := encodeNat_length_le_self (motifLength + motifLength)
  have countBits := encodeNat_length_le_self
    (motifLength + motifLength + 3)
  have additionLimitBits := encodeNat_length_le_self
    (2 * (motifLength + motifLength) + 4)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  change flatStripEncodedListSpaceInputCost fields ≤ _
  have fieldTwo : fields[2]?.getD 0 = motifLength := by
    simp [fields, motifLength, PeriodicStripFlatEncoding.stripFields]
  simp only [flatStripEncodedListSpaceInputCost,
    flatStripFieldCountCost, fieldTwo, prependCost, List.headI_cons]
  simp [flatStripParameterComponentBound,
    inputLength, motifLength,
    fields, PeriodicStripFlatEncoding.stripFields,
    encodedListSpace_cons, encodedListSpace_nil, zeroBits]
    at inputSpace motifLengthBound get2 zero identity addition addConstant
      motifBits doubledBits countBits additionLimitBits ⊢
  simp only [fields, PeriodicStripFlatEncoding.stripFields] at fieldTwo
  rw [fieldTwo] at *
  omega

set_option maxHeartbeats 1000000 in
theorem flatStripEncodedListSpaceCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripEncodedListSpaceCost periodicStrip ≤
      2 * flatStripParameterComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have input := flatStripEncodedListSpaceInputCost_le_input periodicStrip
  have fieldsSpace : encodedListSpace
      (PeriodicStripFlatEncoding.stripFields periodicStrip) =
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
    simp [PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
  simp only [flatStripEncodedListSpaceCost,
    encodedListSpaceLoopSpaceBound, encodedListSpaceStepSpaceBound,
    flatStripParameterComponentBound] at input ⊢
  rw [fieldsSpace]
  omega

theorem flatStripSearchDepthCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripSearchDepthCost periodicStrip ≤
      10 * flatStripParameterComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have fieldsSpace : encodedListSpace fields = inputLength := by
    simp [fields, inputLength,
      PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
  have encodedCost := flatStripEncodedListSpaceCost_le_input periodicStrip
  have oneCostBound := StripSavitchStep.oneCost_le_linear fields
  have inputLengthBits := encodeNat_length_le_self inputLength
  have inputLengthDef :
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length =
        inputLength := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  change flatStripSearchDepthLoopCost inputLength +
      flatStripSearchDepthInputCost periodicStrip ≤ _
  simp only [flatStripSearchDepthLoopCost,
    flatStripSearchDepthInputCost, prependCost, List.headI_cons]
  simp [fields, inputLength, encodedListSpace_cons,
    encodedListSpace_nil, oneBits] at fieldsSpace encodedCost oneCostBound ⊢
  simp only [flatStripParameterComponentBound] at encodedCost ⊢
  rw [inputLengthDef] at *
  omega

theorem flatStripPowerTwoCost_le_input
    (periodicStrip : PeriodicStrip) :
    powerTwoCost (flatStripSearchDepth periodicStrip) ≤
      flatStripParameterComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let depth := flatStripSearchDepth periodicStrip
  have depthEq : depth = 21 * inputLength + 1 := by
    rfl
  have depthBits := encodeNat_length_le_self depth
  have depthSuccessorBits := encodeNat_succ_length_le depth
  have stateBoundPow : 2 ^ depth < 2 ^ (depth + 1) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have stateBoundBits := Turing.PartrecToTM2.encodeNat_length_le_of_lt_pow
    (2 ^ depth) (depth + 1) stateBoundPow
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  change powerTwoCost depth ≤ flatStripParameterComponentBound inputLength
  simp [powerTwoCost, powerTwoInputCost, powerTwoLoopCost,
    prependCost, idCost, headCost, nilCost, oneCost,
    zeroCost, zeroPrimeCost, tailCost, succCost,
    flatStripParameterComponentBound,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits] at depthBits depthSuccessorBits stateBoundBits ⊢
  omega

theorem flatStripStateBoundCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripStateBoundCost periodicStrip ≤
      11 * flatStripParameterComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have power := flatStripPowerTwoCost_le_input periodicStrip
  have depth := flatStripSearchDepthCost_le_input periodicStrip
  simp only [flatStripStateBoundCost]
  omega

theorem flatStripCycleParametersCost_le_input
    (periodicStrip : PeriodicStrip) :
    flatStripCycleParametersCost periodicStrip ≤
      flatStripParameterSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let depth := flatStripSearchDepth periodicStrip
  let stateBound := flatStripStateBound periodicStrip
  have fieldsSpace : encodedListSpace fields = inputLength := by
    simp [fields, inputLength,
      PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
  have depthCost := flatStripSearchDepthCost_le_input periodicStrip
  have stateCost := flatStripStateBoundCost_le_input periodicStrip
  have identity := StripSavitchStep.idCost_le_linear fields
  have depthEq : depth = 21 * inputLength + 1 := by rfl
  have depthBits := encodeNat_length_le_self depth
  have stateBoundPow : stateBound < 2 ^ (depth + 1) := by
    simp only [stateBound, flatStripStateBound]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have stateBoundBits := Turing.PartrecToTM2.encodeNat_length_le_of_lt_pow
    stateBound (depth + 1) stateBoundPow
  change flatStripCycleParametersCost periodicStrip ≤ _
  simp only [flatStripCycleParametersCost, prependCost, List.headI_cons]
  simp [fields, inputLength, depth, stateBound,
    encodedListSpace_cons, encodedListSpace_nil]
    at fieldsSpace depthCost stateCost identity depthBits stateBoundBits ⊢
  simp only [flatStripParameterSpaceBound,
    flatStripParameterComponentBound] at depthCost stateCost ⊢
  omega

def flatPeriodicStripTrominoTilingSpaceBound (inputLength : Nat) : Nat :=
  1000000 *
    (FlatStripCyclePartrec.flatStripCycleSearchSpaceBound inputLength +
      flatStripParameterSpaceBound inputLength +
      flatStripWellFormedSpaceBound inputLength + inputLength + 1)

noncomputable def flatPeriodicStripTrominoTilingSpacePolynomial :
    Polynomial Nat :=
  1000000 *
    (flatStripCycleSearchSpacePolynomial +
      1000000000 *
        (1000000000000000000000000000000000000000000000000000000000000 *
          (Polynomial.X + 1)) +
      3 *
        (1000000000000000000000000000000000000000000000000000000000000 *
          (Polynomial.X + 1)) +
      Polynomial.X + 1)

@[simp] theorem flatPeriodicStripTrominoTilingSpacePolynomial_eval
    (inputLength : Nat) :
    flatPeriodicStripTrominoTilingSpacePolynomial.eval inputLength =
      flatPeriodicStripTrominoTilingSpaceBound inputLength := by
  simp [flatPeriodicStripTrominoTilingSpacePolynomial,
    flatPeriodicStripTrominoTilingSpaceBound,
    flatStripParameterSpaceBound, flatStripParameterComponentBound,
    flatStripWellFormedSpaceBound, flatStripGuardLoopSpaceBound]

set_option maxHeartbeats 1000000 in
theorem flatPeriodicStripTrominoTilingCost_le_spaceBound
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    flatPeriodicStripTrominoTilingCost tromino periodicStrip ≤
      flatPeriodicStripTrominoTilingSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let fields := PeriodicStripFlatEncoding.stripFields periodicStrip
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have fieldsSpace : encodedListSpace fields = inputLength := by
    simp [fields, inputLength,
      PeriodicStripFlatEncoding.finEncoding_encode_length,
      encodedListSpace_eq_sum]
  have guardSpace := congrArg flatStripWellFormedSpaceBound fieldsSpace
  have parameterCost := flatStripCycleParametersCost_le_input periodicStrip
  have identity := StripSavitchStep.idCost_le_linear fields
  have zeroBranch := listCodeZeroCost_le_linear fields
  have testZeroTail := listCodeTailCost_le_linear (0 :: fields)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  by_cases wellFormed : periodicStrip.IsWellFormed
  · have wellFormedBool : periodicStrip.wellFormed = true :=
      (periodicStrip.wellFormed_eq_true_iff).mpr wellFormed
    let result := flatPeriodicStripTrominoTilingBool tromino periodicStrip
    have outputSpace : encodedListSpace [Encodable.encode result] ≤ 2 := by
      cases result <;> decide
    change flatPeriodicStripTrominoTilingCost tromino periodicStrip ≤ _
    simp only [flatPeriodicStripTrominoTilingCost, dif_pos wellFormed,
      flatStripCycleBranchCost, branchZeroSuccCost,
      branchZeroZeroCost, branchZeroTestCost, prependCost,
      List.headI_cons]
    simp [fields, inputLength, result, wellFormedBool,
      encodedListSpace_cons, encodedListSpace_nil, zeroBits, oneBits]
      at fieldsSpace parameterCost identity zeroBranch testZeroTail
        guardSpace outputSpace ⊢
    simp only [flatPeriodicStripTrominoTilingSpaceBound] at ⊢
    omega
  · have wellFormedBool : periodicStrip.wellFormed = false := by
      apply Bool.eq_false_iff.mpr
      intro true
      exact wellFormed
        ((periodicStrip.wellFormed_eq_true_iff).mp true)
    have outputSpace : encodedListSpace
        [Encodable.encode
          (flatPeriodicStripTrominoTilingBool tromino periodicStrip)] ≤ 2 := by
      simpa [flatPeriodicStripTrominoTilingBool, wellFormed,
        encodedListSpace_cons, encodedListSpace_nil, zeroBits]
    change flatPeriodicStripTrominoTilingCost tromino periodicStrip ≤ _
    simp only [flatPeriodicStripTrominoTilingCost, dif_neg wellFormed,
      branchZeroZeroCost, branchZeroTestCost, prependCost,
      List.headI_cons]
    simp [fields, inputLength, wellFormedBool,
      flatPeriodicStripTrominoTilingBool, wellFormed,
      encodedListSpace_cons, encodedListSpace_nil, zeroBits, oneBits]
      at fieldsSpace parameterCost identity zeroBranch testZeroTail
        guardSpace outputSpace ⊢
    simp only [flatPeriodicStripTrominoTilingSpaceBound] at ⊢
    omega

/-- Complete native-flat decider under its explicit polynomial reserve. -/
theorem flatPeriodicStripTrominoTiling_fits_polynomial
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits (flatPeriodicStripTrominoTilingCode tromino)
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      [Encodable.encode
        (flatPeriodicStripTrominoTilingBool tromino periodicStrip)]
      (flatPeriodicStripTrominoTilingSpacePolynomial.eval
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) := by
  rw [flatPeriodicStripTrominoTilingSpacePolynomial_eval]
  exact (flatPeriodicStripTrominoTiling_fits tromino periodicStrip).mono
    (flatPeriodicStripTrominoTilingCost_le_spaceBound
      tromino periodicStrip)

/-- Complete run-level certificate for the native-flat evaluator. -/
theorem flatPeriodicStripTrominoTiling_run_fits
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    EvaluatorRunFits (flatPeriodicStripTrominoTilingCode tromino)
      (PeriodicStripFlatEncoding.stripFields periodicStrip)
      (flatPeriodicStripTrominoTilingSpacePolynomial.eval
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) := by
  have fit := flatPeriodicStripTrominoTiling_fits_polynomial
    tromino periodicStrip
  let bound := flatPeriodicStripTrominoTilingSpacePolynomial.eval
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have after : EvaluatorExecutionFits bound
      (.ret Turing.ToPartrec.Cont.halt
        [Encodable.encode
          (flatPeriodicStripTrominoTilingBool tromino periodicStrip)]) :=
    EvaluatorExecutionFits.ret_halt (by
      simpa [bound] using fit.output_space)
  have call := fit.call Turing.ToPartrec.Cont.halt bound (by
    simp [bound, continuationSpace, trContStack]) after
  exact EvaluatorRunFits.of_call call

/-- Explicit polynomial-space decider for periodic strip tiling under the
target native flat encoding. -/
noncomputable def flatPeriodicStripTrominoTiling_deciderInPolySpace
    (tromino : Tromino) :
    Complexity.DeciderInPolySpace PeriodicStripFlatEncoding.finEncoding
      (PeriodicStripTrominoTiling tromino) := by
  simpa [PeriodicStripFlatEncoding.finEncoding] using
    Turing.PartrecToTM2.deciderInPolySpace_of_flatEvaluatorRunFits
      PeriodicStripFlatEncoding.stripFields
      PeriodicStripFlatEncoding.decodeStripFields
      PeriodicStripFlatEncoding.decodeStripFields_stripFields
      (flatPeriodicStripTrominoTilingCode tromino)
      (flatPeriodicStripTrominoTilingBool tromino)
      (flatPeriodicStripTrominoTilingBool_eq_true_iff tromino)
      (fun periodicStrip => by
        simpa using congrArg (fun result =>
          [Encodable.encode
            (flatPeriodicStripTrominoTilingBool tromino periodicStrip)] ∈
              result)
          (flatPeriodicStripTrominoTilingCode_eval
            tromino periodicStrip))
      flatPeriodicStripTrominoTilingSpacePolynomial
      (flatPeriodicStripTrominoTiling_run_fits tromino)

/-- The 1.5D periodic tromino tiling problem belongs to PSPACE for every
tromino, measured in the target flat presentation encoding. -/
theorem flatPeriodicStripTrominoTiling_inPSPACE (tromino : Tromino) :
    Complexity.InPSPACE PeriodicStripFlatEncoding.finEncoding
      (PeriodicStripTrominoTiling tromino) :=
  ⟨flatPeriodicStripTrominoTiling_deciderInPolySpace tromino⟩

end FlatStripDeciderPartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
