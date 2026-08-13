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

end FlatStripDeciderPartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
