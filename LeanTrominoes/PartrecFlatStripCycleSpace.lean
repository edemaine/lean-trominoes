import LeanTrominoes.PartrecFlatStripCycle
import LeanTrominoes.PartrecFlatStripReachSpace

/-!
# Evaluator-space certificate for native-flat strip cycle search

The two endpoint countdowns retain the native periodic-strip suffix.  This
module fits one candidate update, lifts its uniform bound through both tail
iterations, and bounds the complete parameterized cycle search.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState
namespace FlatStripCyclePartrec

open Computability
open LeanTrominoes.FiniteState
open Turing PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits

attribute [-simp] PeriodicStripFlatEncoding.finEncoding_encode_length

/-- Canonical candidate payload used by the second-endpoint countdown. -/
def candidatePayload (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool) : List Nat :=
  [flatStripStateBound periodicStrip, flatStripSearchDepth periodicStrip,
    first, secondRemaining, divideBoolTag found] ++
      PeriodicStripFlatEncoding.stripFields periodicStrip

/-- Canonical payload used by the first-endpoint countdown. -/
def outerPayload (periodicStrip : PeriodicStrip)
    (firstRemaining : Nat) (found : Bool) : List Nat :=
  [flatStripStateBound periodicStrip, flatStripSearchDepth periodicStrip,
    firstRemaining, divideBoolTag found] ++
      PeriodicStripFlatEncoding.stripFields periodicStrip

/-! ## One candidate -/

private noncomputable def edgeInputFields (values : List Nat) :
    List (StripSavitchStep.FieldFit values) :=
  [StripSavitchStep.zeroField values,
    StripSavitchStep.getField 0 values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.zeroField values,
    StripSavitchStep.getField 2 values,
    StripSavitchStep.predecessorField 3 values]

noncomputable def candidateEdgeInputCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values (edgeInputFields values)
    (values.drop 5) (dropCost 5 values)

theorem candidateEdgeInput_fits (values : List Nat) :
    EvaluatorCodeFits candidateEdgeInputCode values
      ([0, values[0]?.getD 0, 0, 0, 0, values[2]?.getD 0,
        (values[3]?.getD 0).pred] ++ values.drop 5)
      (candidateEdgeInputCost values) := by
  have fit := StripSavitchStep.fields values (edgeInputFields values)
    (drop 5 values)
  simpa [candidateEdgeInputCode, candidateSecond,
    candidateEdgeInputCost, edgeInputFields,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField, StripSavitchStep.zeroField,
    StripSavitchStep.predecessorField] using fit

noncomputable def candidateEdgeCost (tromino : Tromino)
    (periodicStrip : PeriodicStrip) (first secondRemaining : Nat) : Nat :=
  let state := divideEvalInitial 0 first secondRemaining.pred
  flatStripTransitionCost tromino 0 (flatStripStateBound periodicStrip)
      state periodicStrip +
    candidateEdgeInputCost
      (candidatePayload periodicStrip first secondRemaining false)

theorem candidateEdge_fits (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool) :
    EvaluatorCodeFits (candidateEdgeCode tromino)
      (candidatePayload periodicStrip first secondRemaining found)
      [divideBoolTag (indexedTransitionRawBool tromino periodicStrip
        first secondRemaining.pred)]
      (flatStripTransitionCost tromino 0
          (flatStripStateBound periodicStrip)
          (divideEvalInitial 0 first secondRemaining.pred) periodicStrip +
        candidateEdgeInputCost
          (candidatePayload periodicStrip first secondRemaining found)) := by
  let values := candidatePayload periodicStrip first secondRemaining found
  let state := divideEvalInitial 0 first secondRemaining.pred
  have adapted := candidateEdgeInput_fits values
  have leaf := flatStripTransition tromino 0
    (flatStripStateBound periodicStrip) state periodicStrip wellFormed
  have fit := EvaluatorCodeFits.comp leaf adapted
  have tagEq :
      (indexedTransitionRawBool tromino periodicStrip first
        secondRemaining.pred).toNat =
      divideBoolTag (indexedTransitionRawBool tromino periodicStrip first
        secondRemaining.pred) := by
    cases indexedTransitionRawBool tromino periodicStrip first
      secondRemaining.pred <;> rfl
  rw [← tagEq]
  simpa [candidateEdgeCode, values, candidatePayload, state,
    divideEvalProgramList, divideEvalInitial,
    DivideEvalState.toNatList, divideOptionBoolTag,
    divideStackToNatList] using fit

private noncomputable def reachInputFields (values : List Nat) :
    List (StripSavitchStep.FieldFit values) :=
  [StripSavitchStep.getField 0 values,
    StripSavitchStep.getField 1 values,
    StripSavitchStep.predecessorField 3 values,
    StripSavitchStep.getField 2 values]

noncomputable def candidateReachInputCost (values : List Nat) : Nat :=
  StripSavitchStep.fieldsCost values (reachInputFields values)
    (values.drop 5) (dropCost 5 values)

theorem candidateReachInput_fits (values : List Nat) :
    EvaluatorCodeFits candidateReachInputCode values
      ([values[0]?.getD 0, values[1]?.getD 0,
        (values[3]?.getD 0).pred, values[2]?.getD 0] ++ values.drop 5)
      (candidateReachInputCost values) := by
  have fit := StripSavitchStep.fields values (reachInputFields values)
    (drop 5 values)
  simpa [candidateReachInputCode, candidateSecond,
    candidateReachInputCost, reachInputFields,
    StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField,
    StripSavitchStep.predecessorField] using fit

theorem candidateReach_fits (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (candidateReachCode tromino)
      (candidatePayload periodicStrip first secondRemaining found)
      [divideBoolTag
        (divideReachIndexDFSBool (flatStripStateBound periodicStrip)
          (indexedTransitionRawBool tromino periodicStrip)
          (flatStripSearchDepth periodicStrip) secondRemaining.pred first)]
      (flatStripReachCallSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
        candidateReachInputCost
          (candidatePayload periodicStrip first secondRemaining found)) := by
  let values := candidatePayload periodicStrip first secondRemaining found
  have secondBelow : secondRemaining.pred <
      flatStripStateBound periodicStrip :=
    (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have query := flatStripReachBool_fits_polynomial tromino periodicStrip
    wellFormed secondRemaining.pred first secondBelow firstBelow
  have adapted := candidateReachInput_fits values
  have fit := EvaluatorCodeFits.comp query adapted
  simpa [candidateReachCode, values, candidatePayload] using fit

noncomputable def candidateFoundCost (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool) : Nat :=
  let values := candidatePayload periodicStrip first secondRemaining found
  let edge := indexedTransitionRawBool tromino periodicStrip first
    secondRemaining.pred
  let reachable := divideReachIndexDFSBool
    (flatStripStateBound periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (flatStripSearchDepth periodicStrip) secondRemaining.pred first
  let edgeCost := flatStripTransitionCost tromino 0
      (flatStripStateBound periodicStrip)
      (divideEvalInitial 0 first secondRemaining.pred) periodicStrip +
    candidateEdgeInputCost values
  let reachCost := flatStripReachCallSpaceBound
      (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
    candidateReachInputCost values
  let bothCost := boolAndCost values (divideBoolTag edge)
    (divideBoolTag reachable) edgeCost reachCost
  boolOrCost values (divideBoolTag found) (divideBoolTag (edge && reachable))
    (getCost 4 values) bothCost

theorem candidateFound_fits (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (candidateFoundCode tromino)
      (candidatePayload periodicStrip first secondRemaining found)
      [divideBoolTag
        (found || cycleCandidateBool tromino periodicStrip
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip)
          first secondRemaining.pred)]
      (candidateFoundCost tromino periodicStrip first secondRemaining found) := by
  let values := candidatePayload periodicStrip first secondRemaining found
  let edgeValue := indexedTransitionRawBool tromino periodicStrip first
    secondRemaining.pred
  let reachValue := divideReachIndexDFSBool
    (flatStripStateBound periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (flatStripSearchDepth periodicStrip) secondRemaining.pred first
  have edgeFit := candidateEdge_fits tromino periodicStrip wellFormed
    first secondRemaining found
  have reachFit := candidateReach_fits tromino periodicStrip wellFormed
    first secondRemaining found firstBelow secondPositive secondBound
  have both := EvaluatorCodeFits.boolAnd edgeFit reachFit
  have bothTag :
      (if divideBoolTag edgeValue = 0 ∨ divideBoolTag reachValue = 0
        then 0 else 1) = divideBoolTag (edgeValue && reachValue) := by
    cases edgeValue <;> cases reachValue <;> rfl
  rw [bothTag] at both
  have old : EvaluatorCodeFits (ToPartrec.Code.get 4) values
      [divideBoolTag found] (getCost 4 values) := by
    simpa [values, candidatePayload] using EvaluatorCodeFits.get 4 values
  have accumulated := EvaluatorCodeFits.boolOr old both
  have accumulatedTag :
      (if divideBoolTag found = 0 ∧
          divideBoolTag (edgeValue && reachValue) = 0 then 0 else 1) =
        divideBoolTag (found || (edgeValue && reachValue)) := by
    cases found <;> cases edgeValue <;> cases reachValue <;> rfl
  rw [accumulatedTag] at accumulated
  simpa [candidateFoundCode, candidateFoundCost, values,
    edgeValue, reachValue, cycleCandidateBool] using accumulated

private noncomputable def candidateFoundField
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    StripSavitchStep.FieldFit
      (candidatePayload periodicStrip first secondRemaining found) where
  code := candidateFoundCode tromino
  output := divideBoolTag
    (found || cycleCandidateBool tromino periodicStrip
      (flatStripStateBound periodicStrip)
      (flatStripSearchDepth periodicStrip) first secondRemaining.pred)
  cost := candidateFoundCost tromino periodicStrip first secondRemaining found
  fits := candidateFound_fits tromino periodicStrip wellFormed
    first secondRemaining found firstBelow secondPositive secondBound

private noncomputable def candidateStepFields
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    List (StripSavitchStep.FieldFit
      (candidatePayload periodicStrip first secondRemaining found)) :=
  let values := candidatePayload periodicStrip first secondRemaining found
  [StripSavitchStep.getField 0 values,
    StripSavitchStep.getField 1 values,
    StripSavitchStep.getField 2 values,
    StripSavitchStep.predecessorField 3 values,
    candidateFoundField tromino periodicStrip wellFormed
      first secondRemaining found firstBelow secondPositive secondBound]

noncomputable def candidateStepCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) : Nat :=
  let values := candidatePayload periodicStrip first secondRemaining found
  StripSavitchStep.fieldsCost values
    (candidateStepFields tromino periodicStrip wellFormed
      first secondRemaining found firstBelow secondPositive secondBound)
    (values.drop 5) (dropCost 5 values)

theorem candidateStep_fits (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (candidateStepCode tromino)
      (candidatePayload periodicStrip first secondRemaining found)
      (candidatePayload periodicStrip first secondRemaining.pred
        (found || cycleCandidateBool tromino periodicStrip
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip)
          first secondRemaining.pred))
      (candidateStepCost tromino periodicStrip wellFormed
        first secondRemaining found firstBelow secondPositive secondBound) := by
  let values := candidatePayload periodicStrip first secondRemaining found
  let fields := candidateStepFields tromino periodicStrip wellFormed
    first secondRemaining found firstBelow secondPositive secondBound
  have fit := StripSavitchStep.fields values fields (drop 5 values)
  simpa [candidateStepCode, candidateSecond, candidateStepCost,
    candidateStepFields, candidatePayload, values, fields,
    candidateFoundField, StripSavitchStep.fieldsCost,
    FiniteState.DivideEvalPartrec.fields,
    FiniteState.DivideEvalPartrec.field,
    FiniteState.DivideEvalPartrec.predecessorField,
    StripSavitchStep.getField,
    StripSavitchStep.predecessorField] using fit

/-! ## Uniform candidate bound -/

/-- Common list-footprint reserve for every endpoint-scan payload and fixed
adapter output. -/
def flatStripCycleListSpaceBound (inputLength : Nat) : Nat :=
  100 * (flatStripReachQuerySpaceBound inputLength +
    flatStripReachStateSpaceBound inputLength + 1)

theorem candidatePayload_space_le
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    encodedListSpace
        (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have query := flatStripReachQuerySpace_le periodicStrip first first
    firstBelow firstBelow
  have secondBits := encodeNat_length_mono secondBound
  have boolBits : (Computability.encodeNat (divideBoolTag found)).length ≤ 1 := by
    cases found <;> decide
  change encodedListSpace
      (candidatePayload periodicStrip first secondRemaining found) ≤
    flatStripCycleListSpaceBound inputLength
  simp [candidatePayload, encodedListSpace_append,
    encodedListSpace_cons, encodedListSpace_nil, inputLength,
    flatStripCycleListSpaceBound] at query secondBits boolBits ⊢
  omega

theorem outerPayload_space_le
    (periodicStrip : PeriodicStrip)
    (firstRemaining : Nat) (found : Bool)
    (firstBound : firstRemaining ≤ flatStripStateBound periodicStrip) :
    encodedListSpace (outerPayload periodicStrip firstRemaining found) ≤
      flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  have positive : 0 < flatStripStateBound periodicStrip := by
    simp [flatStripStateBound]
  have query := flatStripReachQuerySpace_le periodicStrip 0 0
    positive positive
  have firstBits := encodeNat_length_mono firstBound
  have boolBits : (Computability.encodeNat (divideBoolTag found)).length ≤ 1 := by
    cases found <;> decide
  change encodedListSpace
      (outerPayload periodicStrip firstRemaining found) ≤
    flatStripCycleListSpaceBound inputLength
  simp [outerPayload, encodedListSpace_append,
    encodedListSpace_cons, encodedListSpace_nil, inputLength,
    flatStripCycleListSpaceBound] at query firstBits boolBits ⊢
  omega

theorem candidateCounted_space_le
    (periodicStrip : PeriodicStrip)
    (remaining first secondRemaining : Nat) (found : Bool)
    (remainingBound : remaining ≤ flatStripStateBound periodicStrip)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    encodedListSpace
        (remaining :: candidatePayload periodicStrip first secondRemaining found) ≤
      4 * (flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length + 1) := by
  let values := candidatePayload periodicStrip first secondRemaining found
  have valuesBound : encodedListSpace values ≤
      flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
    simpa [values] using candidatePayload_space_le periodicStrip
      first secondRemaining found firstBelow secondBound
  have counterBits := encodeNat_length_mono remainingBound
  have countHead := encodedListSpace_singleton_headI_le values
  have countHead' :
      (Computability.encodeNat (flatStripStateBound periodicStrip)).length + 1 ≤
        encodedListSpace values + 1 := by
    simpa [values, candidatePayload] using countHead
  change encodedListSpace (remaining :: values) ≤ _
  simp only [encodedListSpace_cons]
  omega

theorem outerCounted_space_le
    (periodicStrip : PeriodicStrip)
    (remaining firstRemaining : Nat) (found : Bool)
    (remainingBound : remaining ≤ flatStripStateBound periodicStrip)
    (firstBound : firstRemaining ≤ flatStripStateBound periodicStrip) :
    encodedListSpace
        (remaining :: outerPayload periodicStrip firstRemaining found) ≤
      4 * (flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length + 1) := by
  let values := outerPayload periodicStrip firstRemaining found
  have valuesBound : encodedListSpace values ≤
      flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
    simpa [values] using outerPayload_space_le periodicStrip
      firstRemaining found firstBound
  have counterBits := encodeNat_length_mono remainingBound
  have countHead := encodedListSpace_singleton_headI_le values
  have countHead' :
      (Computability.encodeNat (flatStripStateBound periodicStrip)).length + 1 ≤
        encodedListSpace values + 1 := by
    simpa [values, outerPayload] using countHead
  change encodedListSpace (remaining :: values) ≤ _
  simp only [encodedListSpace_cons]
  omega

private theorem edgeStateSpace_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first second : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondBelow : second < flatStripStateBound periodicStrip) :
    encodedListSpace
        (divideEvalProgramList 0 (flatStripStateBound periodicStrip)
          (divideEvalInitial 0 first second) ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripReachStateSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have canonical := flatStripReachStateSpace_le tromino periodicStrip
    first second 0 firstBelow secondBelow
  have depthBits := encodeNat_length_mono
    (Nat.zero_le (flatStripSearchDepth periodicStrip))
  simp [divideEvalProgramList, divideEvalInitial,
    DivideEvalState.toNatList, divideOptionBoolTag,
    divideStackToNatList, encodedListSpace_append,
    encodedListSpace_cons, encodedListSpace_nil] at canonical depthBits ⊢
  omega

/-- Uniform reserve for every fixed-width adapter around one candidate. -/
def flatStripCycleAdapterSpaceBound (inputLength : Nat) : Nat :=
  1000000000 * (flatStripCycleListSpaceBound inputLength + 1)

private theorem edgeInputOutput_space_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    encodedListSpace
        ([0, flatStripStateBound periodicStrip, 0, 0, 0, first,
          secondRemaining.pred] ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripCycleListSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have secondBelow : secondRemaining.pred <
      flatStripStateBound periodicStrip :=
    (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have state := edgeStateSpace_le tromino periodicStrip first
    secondRemaining.pred firstBelow secondBelow
  simpa [divideEvalProgramList, divideEvalInitial,
    DivideEvalState.toNatList, divideOptionBoolTag,
    divideStackToNatList] using state.trans (by
      simp [flatStripCycleListSpaceBound]
      omega)

set_option maxHeartbeats 500000 in
theorem candidateEdgeInputCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    candidateEdgeInputCost
        (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleAdapterSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := candidatePayload periodicStrip first secondRemaining found
  let unit := flatStripCycleListSpaceBound inputLength
  have valuesBound : encodedListSpace values ≤ unit := by
    simpa [values, unit, inputLength] using candidatePayload_space_le
      periodicStrip first secondRemaining found firstBelow secondBound
  have outputBound : encodedListSpace
      ((edgeInputFields values).map StripSavitchStep.FieldFit.output ++
        values.drop 5) ≤ unit := by
    have raw := edgeInputOutput_space_le tromino periodicStrip
      first secondRemaining firstBelow secondPositive secondBound
    simpa [edgeInputFields, values, candidatePayload,
      StripSavitchStep.getField, StripSavitchStep.zeroField,
      StripSavitchStep.predecessorField, inputLength, unit] using raw
  have assembled := StripSavitchStep.fieldsCost_le_of values
    (edgeInputFields values) (values.drop 5) (dropCost 5 values)
    unit valuesBound outputBound
  have get0 := StripSavitchStep.getCost_le_budget 0 values unit
    (by omega) valuesBound
  have get2 := StripSavitchStep.getCost_le_budget 2 values unit
    (by omega) valuesBound
  have zero := StripSavitchStep.zeroCost_le_budget values unit valuesBound
  have pred3 := StripSavitchStep.predecessorFieldCost_le_budget
    3 values unit (by omega) valuesBound
  change predCost [values[3]?.getD 0] + getCost 3 values ≤
    30000000 * (unit + 1) at pred3
  have dropped := StripSavitchStep.dropCost_le_budget
    5 values unit (by omega) valuesBound
  change candidateEdgeInputCost values ≤
    flatStripCycleAdapterSpaceBound inputLength
  simp [candidateEdgeInputCost, edgeInputFields,
    StripSavitchStep.getField, StripSavitchStep.zeroField,
    unit, flatStripCycleAdapterSpaceBound] at assembled ⊢
  omega

set_option maxHeartbeats 500000 in
theorem candidateReachInputCost_le
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    candidateReachInputCost
        (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleAdapterSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := candidatePayload periodicStrip first secondRemaining found
  let unit := flatStripCycleListSpaceBound inputLength
  have valuesBound : encodedListSpace values ≤ unit := by
    simpa [values, unit, inputLength] using candidatePayload_space_le
      periodicStrip first secondRemaining found firstBelow secondBound
  have secondBelow : secondRemaining.pred <
      flatStripStateBound periodicStrip :=
    (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have outputBound : encodedListSpace
      ((reachInputFields values).map StripSavitchStep.FieldFit.output ++
        values.drop 5) ≤ unit := by
    have raw := flatStripReachQuerySpace_le periodicStrip
      secondRemaining.pred first secondBelow firstBelow
    exact (by
      simpa [reachInputFields, values, candidatePayload,
        StripSavitchStep.getField, StripSavitchStep.predecessorField,
        inputLength, unit] using raw.trans (by
          simp [flatStripCycleListSpaceBound]
          omega))
  have assembled := StripSavitchStep.fieldsCost_le_of values
    (reachInputFields values) (values.drop 5) (dropCost 5 values)
    unit valuesBound outputBound
  have get0 := StripSavitchStep.getCost_le_budget 0 values unit
    (by omega) valuesBound
  have get1 := StripSavitchStep.getCost_le_budget 1 values unit
    (by omega) valuesBound
  have get2 := StripSavitchStep.getCost_le_budget 2 values unit
    (by omega) valuesBound
  have pred3 := StripSavitchStep.predecessorFieldCost_le_budget
    3 values unit (by omega) valuesBound
  change predCost [values[3]?.getD 0] + getCost 3 values ≤
    30000000 * (unit + 1) at pred3
  have dropped := StripSavitchStep.dropCost_le_budget
    5 values unit (by omega) valuesBound
  change candidateReachInputCost values ≤
    flatStripCycleAdapterSpaceBound inputLength
  simp [candidateReachInputCost, reachInputFields,
    StripSavitchStep.getField, unit,
    flatStripCycleAdapterSpaceBound] at assembled ⊢
  omega

/-- Common component budget for one edge call, one reverse-reachability call,
and their Boolean composition. -/
def flatStripCycleCandidateComponentBound (inputLength : Nat) : Nat :=
  flatStripTransitionUniformSpaceBound inputLength +
    flatStripReachCallSpaceBound inputLength +
    2 * flatStripCycleAdapterSpaceBound inputLength +
    flatStripCycleListSpaceBound inputLength + 10

/-- Boolean-composition reserve inside one candidate update. -/
def flatStripCycleFoundSpaceBound (inputLength : Nat) : Nat :=
  10000000000 *
    (flatStripCycleCandidateComponentBound inputLength + 1)

/-- Uniform polynomial reserve for one complete second-endpoint update. -/
def flatStripCycleCandidateSpaceBound (inputLength : Nat) : Nat :=
  1000000000000 *
    (flatStripCycleCandidateComponentBound inputLength + 1)

private theorem candidateEdgeCost_le_component
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    flatStripTransitionCost tromino 0
          (flatStripStateBound periodicStrip)
          (divideEvalInitial 0 first secondRemaining.pred) periodicStrip +
        candidateEdgeInputCost
          (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleCandidateComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let state := divideEvalInitial 0 first secondRemaining.pred
  have secondBelow : secondRemaining.pred <
      flatStripStateBound periodicStrip :=
    (Nat.pred_lt (Nat.ne_of_gt secondPositive)).trans_le secondBound
  have stateSpace : encodedListSpace
      (divideEvalProgramList 0 (flatStripStateBound periodicStrip) state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) ≤
      flatStripReachStateSpaceBound inputLength := by
    simpa [state, inputLength] using edgeStateSpace_le tromino periodicStrip
      first secondRemaining.pred firstBelow secondBelow
  have indices : state.IndicesBelow
      (flatStripStateBound periodicStrip) := by
    exact divideEvalInitial_indicesBelow
      (flatStripStateBound periodicStrip) 0 first secondRemaining.pred
      firstBelow secondBelow
  have exactToLocal := flatStripTransitionCost_le_bound tromino 0
    (flatStripStateBound periodicStrip) state periodicStrip wellFormed
  have localUniform := flatStripTransitionSpaceBound_le_uniform
    tromino periodicStrip state indices (by
      simpa [inputLength] using stateSpace)
  have edgeBound : flatStripTransitionCost tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip ≤
      flatStripTransitionUniformSpaceBound inputLength := by
    exact exactToLocal.trans (by simpa [inputLength] using localUniform)
  have adapterBound := candidateEdgeInputCost_le tromino periodicStrip
    first secondRemaining found firstBelow secondPositive secondBound
  have adapterBound' : candidateEdgeInputCost
      (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleAdapterSpaceBound inputLength := by
    simpa [inputLength] using adapterBound
  change flatStripTransitionCost tromino 0
      (flatStripStateBound periodicStrip) state periodicStrip +
      candidateEdgeInputCost
        (candidatePayload periodicStrip first secondRemaining found) ≤
    flatStripCycleCandidateComponentBound inputLength
  simp only [flatStripCycleCandidateComponentBound]
  omega

private theorem candidateReachCost_le_component
    (periodicStrip : PeriodicStrip)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    flatStripReachCallSpaceBound
          (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length +
        candidateReachInputCost
          (candidatePayload periodicStrip first secondRemaining found) ≤
      flatStripCycleCandidateComponentBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  have adapter := candidateReachInputCost_le periodicStrip
    first secondRemaining found firstBelow secondPositive secondBound
  simp only [flatStripCycleCandidateComponentBound]
  omega

set_option maxHeartbeats 1000000 in
theorem candidateFoundCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    candidateFoundCost tromino periodicStrip first secondRemaining found ≤
      flatStripCycleFoundSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := candidatePayload periodicStrip first secondRemaining found
  let edgeValue := indexedTransitionRawBool tromino periodicStrip first
    secondRemaining.pred
  let reachValue := divideReachIndexDFSBool
    (flatStripStateBound periodicStrip)
    (indexedTransitionRawBool tromino periodicStrip)
    (flatStripSearchDepth periodicStrip) secondRemaining.pred first
  let edgeCost := flatStripTransitionCost tromino 0
      (flatStripStateBound periodicStrip)
      (divideEvalInitial 0 first secondRemaining.pred) periodicStrip +
    candidateEdgeInputCost values
  let reachCost := flatStripReachCallSpaceBound inputLength +
    candidateReachInputCost values
  let component := flatStripCycleCandidateComponentBound inputLength
  have listToComponent : flatStripCycleListSpaceBound inputLength ≤
      component := by
    dsimp only [component]
    simp only [flatStripCycleCandidateComponentBound]
    omega
  have valuesBound : encodedListSpace values ≤ component := by
    have raw := candidatePayload_space_le periodicStrip
      first secondRemaining found firstBelow secondBound
    simpa [values, inputLength] using raw.trans listToComponent
  have valuesRoom : encodedListSpace values + 2 ≤ component := by
    have raw := candidatePayload_space_le periodicStrip
      first secondRemaining found firstBelow secondBound
    dsimp only [component]
    simp only [flatStripCycleCandidateComponentBound]
    simpa [values, inputLength] using raw.trans (by omega)
  have headRaw := encodedListSpace_singleton_headI_le values
  have headDirect : (Computability.encodeNat values.headI).length ≤
      encodedListSpace values := by
    simp [values, candidatePayload, encodedListSpace_cons,
      encodedListSpace_nil]
    omega
  have headBound : (Computability.encodeNat values.headI).length ≤
      component := by
    omega
  have successorRaw := encodeNat_succ_length_le values.headI
  have successorRaw' :
      (Computability.encodeNat (values.headI + 1)).length ≤
        (Computability.encodeNat values.headI).length + 1 := by
    simpa [Nat.succ_eq_add_one] using successorRaw
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ component := by
    omega
  have edgeBound : edgeCost ≤ component := by
    simpa [edgeCost, values, inputLength, component] using
      candidateEdgeCost_le_component tromino periodicStrip wellFormed
        first secondRemaining found firstBelow secondPositive secondBound
  have reachBound : reachCost ≤ component := by
    simpa [reachCost, values, inputLength, component] using
      candidateReachCost_le_component periodicStrip first secondRemaining
        found firstBelow secondPositive secondBound
  have edgeTag : divideBoolTag edgeValue ≤ 1 := by
    cases edgeValue <;> decide
  have reachTag : divideBoolTag reachValue ≤ 1 := by
    cases reachValue <;> decide
  have bothBound := boolAndCost_le_budget values
    (divideBoolTag edgeValue) (divideBoolTag reachValue)
    edgeCost reachCost component edgeTag reachTag valuesBound
    headBound headSuccessorBound edgeBound reachBound (by
      simp [component, flatStripCycleCandidateComponentBound])
  let secondBudget := 1000000 * (component + 1)
  have secondPositive : 1 ≤ secondBudget := by
    dsimp only [secondBudget]
    omega
  have componentSecond : component ≤ secondBudget := by
    simp [secondBudget]
    omega
  have valuesSecond := valuesBound.trans componentSecond
  have headSecond := headBound.trans componentSecond
  have headSuccessorSecond := headSuccessorBound.trans componentSecond
  have get4 := StripSavitchStep.getCost_le_budget 4 values component
    (by omega) valuesBound
  have get4Second : getCost 4 values ≤ secondBudget :=
    get4.trans (by dsimp only [secondBudget]; omega)
  have bothSecond : boolAndCost values
      (divideBoolTag edgeValue) (divideBoolTag reachValue)
      edgeCost reachCost ≤ secondBudget :=
    bothBound.trans (by dsimp only [secondBudget]; omega)
  have foundTag : divideBoolTag found ≤ 1 := by
    cases found <;> decide
  have bothTag : divideBoolTag (edgeValue && reachValue) ≤ 1 := by
    cases edgeValue <;> cases reachValue <;> decide
  have combined := boolOrCost_le_budget values
    (divideBoolTag found) (divideBoolTag (edgeValue && reachValue))
    (getCost 4 values)
    (boolAndCost values (divideBoolTag edgeValue)
      (divideBoolTag reachValue) edgeCost reachCost)
    secondBudget foundTag bothTag valuesSecond headSecond
    headSuccessorSecond get4Second bothSecond secondPositive
  change candidateFoundCost tromino periodicStrip
      first secondRemaining found ≤
    flatStripCycleFoundSpaceBound inputLength
  simpa [candidateFoundCost, values, edgeValue, reachValue,
    edgeCost, reachCost, flatStripCycleFoundSpaceBound,
    secondBudget, component] using combined.trans (by omega)

set_option maxHeartbeats 1000000 in
theorem candidateStepCost_le
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    candidateStepCost tromino periodicStrip wellFormed
        first secondRemaining found firstBelow secondPositive secondBound ≤
      flatStripCycleCandidateSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length := by
  let inputLength :=
    (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length
  let values := candidatePayload periodicStrip first secondRemaining found
  let unit := flatStripCycleListSpaceBound inputLength
  let fields := candidateStepFields tromino periodicStrip wellFormed
    first secondRemaining found firstBelow secondPositive secondBound
  let result := found || cycleCandidateBool tromino periodicStrip
    (flatStripStateBound periodicStrip) (flatStripSearchDepth periodicStrip)
    first secondRemaining.pred
  have valuesBound : encodedListSpace values ≤ unit := by
    simpa [values, unit, inputLength] using candidatePayload_space_le
      periodicStrip first secondRemaining found firstBelow secondBound
  have unitComponent : unit ≤
      flatStripCycleCandidateComponentBound inputLength := by
    dsimp only [unit]
    simp only [flatStripCycleCandidateComponentBound]
    omega
  have outputBound : encodedListSpace
      (fields.map StripSavitchStep.FieldFit.output ++ values.drop 5) ≤ unit := by
    have raw := candidatePayload_space_le periodicStrip first
      secondRemaining.pred result firstBelow
      ((Nat.pred_le secondRemaining).trans secondBound)
    simpa [fields, candidateStepFields, values, candidatePayload, result,
      candidateFoundField, StripSavitchStep.getField,
      StripSavitchStep.predecessorField, inputLength, unit] using raw
  have assembled := StripSavitchStep.fieldsCost_le_of values fields
    (values.drop 5) (dropCost 5 values) unit valuesBound outputBound
  have get0 := StripSavitchStep.getCost_le_budget 0 values unit
    (by omega) valuesBound
  have get1 := StripSavitchStep.getCost_le_budget 1 values unit
    (by omega) valuesBound
  have get2 := StripSavitchStep.getCost_le_budget 2 values unit
    (by omega) valuesBound
  have pred3 := StripSavitchStep.predecessorFieldCost_le_budget
    3 values unit (by omega) valuesBound
  change predCost [values[3]?.getD 0] + getCost 3 values ≤
    30000000 * (unit + 1) at pred3
  have dropped := StripSavitchStep.dropCost_le_budget
    5 values unit (by omega) valuesBound
  have foundBound : candidateFoundCost tromino periodicStrip
      first secondRemaining found ≤
      flatStripCycleFoundSpaceBound inputLength := by
    simpa [inputLength] using candidateFoundCost_le tromino periodicStrip
      wellFormed first secondRemaining found firstBelow secondPositive
      secondBound
  change StripSavitchStep.fieldsCost values fields
      (values.drop 5) (dropCost 5 values) ≤
    flatStripCycleCandidateSpaceBound inputLength
  have sumEq : (fields.map StripSavitchStep.FieldFit.cost).sum =
      getCost 0 values + getCost 1 values + getCost 2 values +
        (predCost [values[3]?.getD 0] + getCost 3 values) +
        candidateFoundCost tromino periodicStrip
          first secondRemaining found := by
    simp [fields, candidateStepFields, candidateFoundField,
      StripSavitchStep.getField, values]
    ring
  have lengthEq : fields.length = 5 := by
    simp [fields, candidateStepFields]
  rw [sumEq, lengthEq] at assembled
  simp only [flatStripCycleFoundSpaceBound] at foundBound
  simp only [flatStripCycleCandidateSpaceBound]
  omega

/-- Polynomial-cost form of one complete candidate update. -/
theorem candidateStep_fits_polynomial
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first secondRemaining : Nat) (found : Bool)
    (firstBelow : first < flatStripStateBound periodicStrip)
    (secondPositive : 0 < secondRemaining)
    (secondBound : secondRemaining ≤ flatStripStateBound periodicStrip) :
    EvaluatorCodeFits (candidateStepCode tromino)
      (candidatePayload periodicStrip first secondRemaining found)
      (candidatePayload periodicStrip first secondRemaining.pred
        (found || cycleCandidateBool tromino periodicStrip
          (flatStripStateBound periodicStrip)
          (flatStripSearchDepth periodicStrip)
          first secondRemaining.pred))
      (flatStripCycleCandidateSpaceBound
        (PeriodicStripFlatEncoding.finEncoding.encode periodicStrip).length) :=
  (candidateStep_fits tromino periodicStrip wellFormed first secondRemaining
    found firstBelow secondPositive secondBound).mono
      (candidateStepCost_le tromino periodicStrip wellFormed
        first secondRemaining found firstBelow secondPositive secondBound)

end FlatStripCyclePartrec
end RawWindowState
end PeriodicStrip
end LeanTrominoes
