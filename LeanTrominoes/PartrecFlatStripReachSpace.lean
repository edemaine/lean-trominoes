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

end RawWindowState
end PeriodicStrip
end LeanTrominoes
