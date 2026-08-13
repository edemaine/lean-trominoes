import LeanTrominoes.PartrecFlatStripReach
import LeanTrominoes.PartrecFlatSavitchReachSpace

/-!
# Evaluator-space certificate for native-flat strip reachability

This module fits the four-field reachability adapter that retains the native
periodic-strip suffix, composes it with the exact-fuel Savitch loop, and
projects the normalized Boolean answer.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

open Computability
open LeanTrominoes.FiniteState
open Turing PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

attribute [-simp] PeriodicStripFlatEncoding.finEncoding_encode_length

/-- Exact evaluator cost of the state-count and depth projections feeding the
native-flat fuel program. -/
def flatStripReachFuelArgumentsCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values]
    [] (nilCost values)

theorem flatStripReachFuelArguments_fits (values : List Nat) :
    EvaluatorCodeFits flatStripReachFuelArgumentsCode values
      [values[0]?.getD 0, values[1]?.getD 0]
      (flatStripReachFuelArgumentsCost values) := by
  have fit := StripSavitchStep.fields values
    [StripSavitchStep.getField 0 values,
      StripSavitchStep.getField 1 values]
    (nil values)
  simpa [flatStripReachFuelArgumentsCode,
    flatStripReachFuelArgumentsCost, StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    StripSavitchStep.getField] using fit

/-- Exact evaluator cost of computing the fuel field from a native-flat
reachability request. -/
def flatStripReachFuelCost (values : List Nat) : Nat :=
  divideEvalFuelCost [values[0]?.getD 0, values[1]?.getD 0] +
    flatStripReachFuelArgumentsCost values

theorem flatStripReachFuel_fits (values : List Nat) :
    EvaluatorCodeFits flatStripReachFuelCode values
      [FiniteState.divideEvalFuel
        (values[0]?.getD 0) (values[1]?.getD 0)]
      (flatStripReachFuelCost values) := by
  have fit := EvaluatorCodeFits.comp
    (divideEvalFuel [values[0]?.getD 0, values[1]?.getD 0])
    (flatStripReachFuelArguments_fits values)
  simpa [flatStripReachFuelCode, flatStripReachFuelCost] using fit

private noncomputable def flatStripReachFuelField (values : List Nat) :
    StripSavitchStep.FieldFit values where
  code := flatStripReachFuelCode
  output := FiniteState.divideEvalFuel
    (values[0]?.getD 0) (values[1]?.getD 0)
  cost := flatStripReachFuelCost values
  fits := flatStripReachFuel_fits values

private noncomputable def flatStripReachInputFields (values : List Nat) :
    List (StripSavitchStep.FieldFit values) :=
  [flatStripReachFuelField values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.getField 0 values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.getField 1 values,
    StripSavitchStep.getField 2 values,
    StripSavitchStep.getField 3 values]

/-- Exact evaluator cost of assembling the countdown and initial DFS state
while retaining every field after the four-field request header. -/
noncomputable def flatStripReachInputCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values (flatStripReachInputFields values)
    (values.drop 4) (dropCost 4 values)

theorem flatStripReachInput_fits (values : List Nat) :
    EvaluatorCodeFits flatStripReachInputCode values
      (FiniteState.divideEvalFuel
          (values[0]?.getD 0) (values[1]?.getD 0) ::
        [0, values[0]?.getD 0, 0, 0, values[1]?.getD 0,
          values[2]?.getD 0, values[3]?.getD 0] ++ values.drop 4)
      (flatStripReachInputCost values) := by
  have fit := StripSavitchStep.fields values
    (flatStripReachInputFields values) (drop 4 values)
  simpa [flatStripReachInputCode, flatStripReachInputCost,
    flatStripReachInputFields, flatStripReachFuelField,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    StripSavitchStep.getField, StripSavitchStep.zeroField] using fit

/-- Exact compositional cost of a complete native-flat indexed reachability
query, including initialization, the exact-fuel loop, answer projection, and
Boolean normalization. -/
noncomputable def flatStripReachBoolCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [flatStripStateBound periodicStrip, flatStripSearchDepth periodicStrip,
      first, last] ++ PeriodicStripFlatEncoding.stripFields periodicStrip
  let output := FiniteState.FlatStripSavitchStep.flatProgramList
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
    0 (flatStripStateBound periodicStrip)
    (flatStripReachFinalState tromino periodicStrip
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip) first last)
  predCost
      [FiniteState.divideOptionBoolTag
        (flatStripReachFinalState tromino periodicStrip
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip) first last).answer] +
    (getCost 3 output +
      (flatStripSavitchBodySpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
        flatStripReachInputCost values))

theorem flatStripReachBool_fits
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (flatStripReachBoolCode tromino)
      ([flatStripStateBound periodicStrip,
        flatStripSearchDepth periodicStrip, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip)
      [FiniteState.divideBoolTag
        (FiniteState.divideReachIndexDFSBool
          (flatStripStateBound periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (flatStripSearchDepth periodicStrip) first last)]
      (flatStripReachBoolCost tromino periodicStrip first last) := by
  let suffix := PeriodicStripFlatEncoding.stripFields periodicStrip
  let values := [flatStripStateBound periodicStrip,
    flatStripSearchDepth periodicStrip, first, last] ++ suffix
  let finalState := flatStripReachFinalState tromino periodicStrip
    (flatStripStateBound periodicStrip)
    (flatStripSearchDepth periodicStrip) first last
  let output := FiniteState.FlatStripSavitchStep.flatProgramList suffix
    0 (flatStripStateBound periodicStrip) finalState
  have inputFit : EvaluatorCodeFits flatStripReachInputCode values
      (FiniteState.divideEvalFuel
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip) ::
        FiniteState.FlatStripSavitchStep.flatProgramList suffix
          0 (flatStripStateBound periodicStrip)
          (FiniteState.divideEvalInitial
            (flatStripSearchDepth periodicStrip) first last))
      (flatStripReachInputCost values) := by
    simpa [values, suffix,
      FiniteState.FlatStripSavitchStep.flatProgramList,
      FiniteState.divideEvalProgramList,
      FiniteState.divideEvalInitial,
      FiniteState.DivideEvalState.toNatList,
      FiniteState.divideOptionBoolTag,
      FiniteState.divideStackToNatList] using
      flatStripReachInput_fits values
  have loopFit := flatStripSavitchFlatUniform tromino periodicStrip
    wellFormed first last firstBelow lastBelow
  have loopWithInput := EvaluatorCodeFits.comp loopFit inputFit
  have loopWithInput' :
      EvaluatorCodeFits
        ((Turing.ToPartrec.Code.flatIterate
          (FiniteState.DivideEvalPartrec.stepCode
            (FiniteState.FlatStripEdgePartrec.baseCode tromino))).comp
          flatStripReachInputCode)
        values output
        (flatStripSavitchBodySpaceBound
            (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
          flatStripReachInputCost values) := by
    simpa [finalState, flatStripReachFinalState, output, suffix] using
      loopWithInput
  have projected := EvaluatorCodeFits.comp (get 3 output) loopWithInput'
  have normalized := EvaluatorCodeFits.comp
    (pred_named [FiniteState.divideOptionBoolTag finalState.answer]) projected
  have answerTag :
      (FiniteState.divideOptionBoolTag finalState.answer).pred =
        FiniteState.divideBoolTag (finalState.answer.getD false) := by
    cases finalState.answer with
    | none => rfl
    | some answerValue => cases answerValue <;> rfl
  have outputEq :
      [FiniteState.divideOptionBoolTag finalState.answer - 1] =
        [FiniteState.divideBoolTag
          (FiniteState.divideReachIndexDFSBool
            (flatStripStateBound periodicStrip)
            (indexedTransitionRawBool tromino periodicStrip)
            (flatStripSearchDepth periodicStrip) first last)] := by
    rw [Nat.sub_one, answerTag]
    rfl
  have outputEq' :
      Turing.ToPartrec.Code.subtractStepList
          [FiniteState.divideOptionBoolTag finalState.answer] =
        [FiniteState.divideBoolTag
          (FiniteState.divideReachIndexDFSBool
            (flatStripStateBound periodicStrip)
            (indexedTransitionRawBool tromino periodicStrip)
            (flatStripSearchDepth periodicStrip) first last)] := by
    simpa [Turing.ToPartrec.Code.subtractStepList] using outputEq
  rw [outputEq'] at normalized
  simpa [flatStripReachBoolCode, flatStripReachBoolCost, values, output,
    suffix, finalState, predCost,
    Turing.ToPartrec.Code.subtractStepList] using normalized

/-! ## Uniform native-input bound -/

/-- Loose native-list footprint of one four-field reachability request plus
the complete strip suffix. -/
def flatStripReachQuerySpaceBound (inputLength : Nat) : Nat :=
  100 * inputLength + 100

private theorem flatStripStateBound_encodeNat_length_le
    (periodicStrip : PeriodicStrip) :
    (Computability.encodeNat
      (flatStripStateBound periodicStrip)).length ≤
      flatStripSearchDepth periodicStrip + 1 := by
  apply FiniteState.encodeNat_length_le_of_lt_pow
  exact Nat.pow_lt_pow_right (by omega)
    (show flatStripSearchDepth periodicStrip <
      flatStripSearchDepth periodicStrip + 1 by omega)

theorem flatStripReachQuerySpace_le
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    encodedListSpace
        ([flatStripStateBound periodicStrip,
          flatStripSearchDepth periodicStrip, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripReachQuerySpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let depth := flatStripSearchDepth periodicStrip
  have depthEq : flatStripSearchDepth periodicStrip =
      21 * inputLength + 1 := by rfl
  have countBits := flatStripStateBound_encodeNat_length_le periodicStrip
  have depthBits : (Computability.encodeNat depth).length ≤ depth + 1 := by
    apply FiniteState.encodeNat_length_le_of_lt_pow
    exact flatStripSearchDepth_lt_pow_succ periodicStrip
  have firstBits := flatStripCounter_encodeNat_length_le
    periodicStrip first firstBelow
  have lastBits := flatStripCounter_encodeNat_length_le
    periodicStrip last lastBelow
  have suffixSpace : encodedListSpace
      (PeriodicStripFlatEncoding.stripFields periodicStrip) = inputLength := by
    dsimp only [inputLength]
    rw [encodedListSpace_eq_sum]
    exact (PeriodicStripFlatEncoding.finEncoding_encode_length
      periodicStrip).symm
  have countBits' : (Computability.encodeNat
      (flatStripStateBound periodicStrip)).length ≤
      21 * inputLength + 2 := by
    change (Computability.encodeNat
      (flatStripStateBound periodicStrip)).length ≤
        flatStripSearchDepth periodicStrip + 1 at countBits
    omega
  have depthBits' : (Computability.encodeNat
      (flatStripSearchDepth periodicStrip)).length ≤
      21 * inputLength + 2 := by
    change (Computability.encodeNat
      (flatStripSearchDepth periodicStrip)).length ≤
        flatStripSearchDepth periodicStrip + 1 at depthBits
    omega
  have headerBound : encodedListSpace
      [flatStripStateBound periodicStrip,
        flatStripSearchDepth periodicStrip, first, last] ≤
      99 * inputLength + 99 := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    omega
  calc
    encodedListSpace
        ([flatStripStateBound periodicStrip,
          flatStripSearchDepth periodicStrip, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      encodedListSpace
          [flatStripStateBound periodicStrip,
            flatStripSearchDepth periodicStrip, first, last] +
        inputLength := by
      rw [FiniteState.encodedListSpace_append, suffixSpace]
    _ ≤ 100 * inputLength + 100 := by omega
    _ = flatStripReachQuerySpaceBound inputLength := by
      rfl

/-- Explicit nested-fuel computation reserve measured in the target flat
input length. -/
def flatStripFuelComputationSpaceBound (inputLength : Nat) : Nat :=
  1000000000000000000000000000000000000000000000000000000000000 *
    (flatStripFuelBits inputLength + 100 * inputLength + 100)

set_option maxHeartbeats 1000000 in
theorem flatStripFuelCost_le (periodicStrip : PeriodicStrip) :
    divideEvalFuelCost
        [flatStripStateBound periodicStrip,
          flatStripSearchDepth periodicStrip] ≤
      flatStripFuelComputationSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let stateCount := flatStripStateBound periodicStrip
  let depth := flatStripSearchDepth periodicStrip
  let fuel := FiniteState.divideEvalFuel stateCount depth
  change divideEvalFuelCost [stateCount, depth] ≤
    flatStripFuelComputationSpaceBound inputLength
  have depthEq : depth = 21 * inputLength + 1 := by
    rfl
  have countBits : (Computability.encodeNat stateCount).length ≤
      21 * inputLength + 3 := by
    have localBound := flatStripStateBound_encodeNat_length_le periodicStrip
    change (Computability.encodeNat stateCount).length ≤ depth + 1 at localBound
    omega
  have depthBits : (Computability.encodeNat depth).length ≤
      21 * inputLength + 2 := by
    have localBound : (Computability.encodeNat depth).length ≤ depth + 1 := by
      apply FiniteState.encodeNat_length_le_of_lt_pow
      change flatStripSearchDepth periodicStrip <
        2 ^ (flatStripSearchDepth periodicStrip + 1)
      exact flatStripSearchDepth_lt_pow_succ periodicStrip
    omega
  have fuelBits : (Computability.encodeNat fuel).length ≤
      flatStripFuelBits inputLength := by
    simpa [fuel, stateCount, depth, inputLength] using
      flatStripFuel_encodeNat_length_le periodicStrip
  have countPlusBits :
      (Computability.encodeNat (stateCount + 1)).length ≤
        (Computability.encodeNat stateCount).length + 1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le stateCount
  have depthPlusBits :
      (Computability.encodeNat (depth + 1)).length ≤
        (Computability.encodeNat depth).length + 1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le depth
  have fuelPlusBits :
      (Computability.encodeNat (fuel + 1)).length ≤
        (Computability.encodeNat fuel).length + 1 := by
    simpa [Nat.succ_eq_add_one] using encodeNat_succ_length_le fuel
  have fuelDirectBits :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel stateCount depth)).length ≤
      flatStripFuelBits inputLength := by
    simpa [fuel] using fuelBits
  have fuelPlusDirectBits :
      (Computability.encodeNat
        (FiniteState.divideEvalFuel stateCount depth + 1)).length ≤
      flatStripFuelBits inputLength + 1 := by
    simpa [fuel] using fuelPlusBits.trans (by omega)
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
  dsimp only [inputLength] at countBits depthBits fuelBits fuelDirectBits fuelPlusDirectBits depthEq ⊢
  simp [divideEvalFuelCost, divideEvalFuelInputCost,
    fuelOuterLoopCost, flatStripFuelComputationSpaceBound,
    prependCost, getCost, dropCost, idCost, headCost, nilCost,
    oneCost, zeroCost, zeroPrimeCost, tailCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits, oneBits]
  omega

private theorem flatStripReachNilCost_le_linear (values : List Nat) :
    nilCost values ≤ 1000 * (encodedListSpace values + 1) := by
  have headSpace := encodedListSpace_singleton_headI_le values
  have successorBits := encodeNat_succ_length_le values.headI
  simp [nilCost, tailCost, succCost, encodedListSpace_cons]
    at headSpace successorBits ⊢
  omega

set_option maxHeartbeats 1000000 in
/-- The complete native-suffix input adapter, including exact-fuel
computation, fits one input-polynomial reserve. -/
theorem flatStripReachInputCost_le
    (periodicStrip : PeriodicStrip) (first last : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    flatStripReachInputCost
        ([flatStripStateBound periodicStrip,
          flatStripSearchDepth periodicStrip, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      1000000 *
        (flatStripFuelComputationSpaceBound
            (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
          flatStripReachQuerySpaceBound
            (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
          flatStripReachPayloadSpaceBound
            (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
          1) := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := [flatStripStateBound periodicStrip,
    flatStripSearchDepth periodicStrip, first, last] ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  have inputBound : encodedListSpace values ≤
      flatStripReachQuerySpaceBound inputLength := by
    simpa [values, inputLength] using flatStripReachQuerySpace_le
      periodicStrip first last firstBelow lastBelow
  have outputBound := flatStripReachCountdownSpace_le Tromino.I periodicStrip
    first last 0
    (FiniteState.divideEvalFuel (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip))
    firstBelow lastBelow (Nat.le_refl _)
  have fuelCost := flatStripFuelCost_le periodicStrip
  have outputBound' : encodedListSpace
      (FiniteState.divideEvalFuel (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip) ::
        (FiniteState.divideEvalProgramList 0
          (flatStripStateBound periodicStrip)
          (FiniteState.divideEvalInitial
            (flatStripSearchDepth periodicStrip) first last) ++
          PeriodicStripFlatEncoding.stripFields periodicStrip)) ≤
      flatStripReachPayloadSpaceBound inputLength := by
    simpa [inputLength] using outputBound
  have fuelCost' : divideEvalFuelCost
      [flatStripStateBound periodicStrip,
        flatStripSearchDepth periodicStrip] ≤
      flatStripFuelComputationSpaceBound inputLength := by
    simpa [inputLength] using fuelCost
  have get0 := listCodeGetCost_le_linear 0 values
  have get1 := listCodeGetCost_le_linear 1 values
  have get2 := listCodeGetCost_le_linear 2 values
  have get3 := listCodeGetCost_le_linear 3 values
  have zero := listCodeZeroCost_le_linear values
  have dropped := StripSavitchStep.dropCost_le_linear 4 values
  have nil := flatStripReachNilCost_le_linear values
  change flatStripReachInputCost values ≤
    1000000 *
      (flatStripFuelComputationSpaceBound inputLength +
        flatStripReachQuerySpaceBound inputLength +
        flatStripReachPayloadSpaceBound inputLength + 1)
  simp [flatStripReachInputCost, flatStripReachInputFields,
    flatStripReachFuelField, flatStripReachFuelCost,
    flatStripReachFuelArgumentsCost, StripSavitchStep.fieldsCost,
    prependCost, StripSavitchStep.getField,
    StripSavitchStep.zeroField, values, inputLength,
    FiniteState.divideEvalProgramList,
    FiniteState.divideEvalInitial,
    FiniteState.DivideEvalState.toNatList,
    FiniteState.divideOptionBoolTag,
    FiniteState.divideStackToNatList,
    encodedListSpace_cons, encodedListSpace_nil]
    at inputBound outputBound' fuelCost' get0 get1 get2 get3 zero dropped nil ⊢
  omega

/-- Uniform workspace for one complete native-flat indexed reachability call.
-/
def flatStripReachCallSpaceBound (inputLength : Nat) : Nat :=
  1000000000 *
    (flatStripFuelComputationSpaceBound inputLength +
      flatStripReachQuerySpaceBound inputLength +
      flatStripReachPayloadSpaceBound inputLength +
      flatStripSavitchBodySpaceBound inputLength + 1)

theorem flatStripReachBoolCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first last : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    flatStripReachBoolCost tromino periodicStrip first last ≤
      flatStripReachCallSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := [flatStripStateBound periodicStrip,
    flatStripSearchDepth periodicStrip, first, last] ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let finalState := flatStripReachFinalState tromino periodicStrip
    (flatStripStateBound periodicStrip)
    (flatStripSearchDepth periodicStrip) first last
  let output := FiniteState.FlatStripSavitchStep.flatProgramList
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
    0 (flatStripStateBound periodicStrip) finalState
  have inputCost : flatStripReachInputCost values ≤
      1000000 *
        (flatStripFuelComputationSpaceBound inputLength +
          flatStripReachQuerySpaceBound inputLength +
          flatStripReachPayloadSpaceBound inputLength + 1) := by
    simpa [values, inputLength] using flatStripReachInputCost_le
      periodicStrip first last firstBelow lastBelow
  have outputBound : encodedListSpace output ≤
      flatStripReachPayloadSpaceBound inputLength := by
    have stateBound := flatStripReachStateSpace_le tromino periodicStrip
      first last
      (FiniteState.divideEvalFuel (flatStripStateBound periodicStrip)
        (flatStripSearchDepth periodicStrip))
      firstBelow lastBelow
    have stateBound' : encodedListSpace output ≤
        flatStripReachStateSpaceBound inputLength := by
      simpa [output, finalState, flatStripReachFinalState, inputLength,
        FiniteState.FlatStripSavitchStep.flatProgramList] using stateBound
    exact stateBound'.trans (by
      simp only [flatStripReachPayloadSpaceBound]
      omega)
  have projected := listCodeGetCost_le_linear 3 output
  have queryLarge : 100 ≤ flatStripReachQuerySpaceBound inputLength := by
    simp [flatStripReachQuerySpaceBound]
  have bodyLarge : 100000 ≤
      flatStripSavitchBodySpaceBound inputLength := by
    simp [flatStripSavitchBodySpaceBound]
  have normalized : predCost
      [FiniteState.divideOptionBoolTag finalState.answer] ≤ 1000000 := by
    cases answer : finalState.answer with
    | none => native_decide
    | some answerValue => cases answerValue <;> native_decide
  change flatStripReachBoolCost tromino periodicStrip first last ≤
    flatStripReachCallSpaceBound inputLength
  simp [flatStripReachBoolCost, values, output, finalState, inputLength,
    flatStripReachCallSpaceBound]
    at inputCost outputBound projected normalized queryLarge bodyLarge ⊢
  omega

/-- Polynomial-cost form of the complete native-flat reachability query. -/
theorem flatStripReachBool_fits_polynomial
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (lastBelow : last < flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (flatStripReachBoolCode tromino)
      ([flatStripStateBound periodicStrip,
        flatStripSearchDepth periodicStrip, first, last] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip)
      [FiniteState.divideBoolTag
        (FiniteState.divideReachIndexDFSBool
          (flatStripStateBound periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (flatStripSearchDepth periodicStrip) first last)]
      (flatStripReachCallSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :=
  (flatStripReachBool_fits tromino periodicStrip wellFormed first last
    firstBelow lastBelow).mono
      (flatStripReachBoolCost_le tromino periodicStrip first last
        firstBelow lastBelow)

end RawWindowState
end PeriodicStrip
end LeanTrominoes
