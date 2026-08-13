import LeanTrominoes.PartrecFlatStripTransitionSpace
import LeanTrominoes.StripFrontierPartrecSpace

/-!
# Evaluator-space certificate for one suffix-preserving flat Savitch step

This module reuses the verified structural branch combinators from the legacy
strip evaluator, but charges them against a payload that retains the native
flat strip fields as an arbitrary-length suffix.  The only non-structural
branch is the bounded recovered edge oracle.
-/

namespace LeanTrominoes
namespace FiniteState

open Computability
open Turing
open Turing.PartrecToTM2
open Turing.PartrecToTM2.EvaluatorCodeFits
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState
open LeanTrominoes.PeriodicStrip.RawWindowState.StripSavitchStep

namespace FlatStripSavitchStep

attribute [local simp] FiniteState.divideEvalProgramList

@[simp]
def flatProgramList
    (suffix : List Nat) (context stateCount : Nat)
    (state : DivideEvalState) : List Nat :=
  divideEvalProgramList context stateCount state ++ suffix

def baseBoolCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (context stateCount : Nat) (state : DivideEvalState) : Nat :=
  Turing.PartrecToTM2.EvaluatorCodeFits.flatStripBaseCost
    tromino context stateCount state periodicStrip

theorem baseBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (context stateCount : Nat) (state : DivideEvalState) :
    Turing.PartrecToTM2.EvaluatorCodeFits
      (FlatStripEdgePartrec.baseCode tromino)
      (flatProgramList (PeriodicStripFlatEncoding.stripFields periodicStrip)
        context stateCount state)
      [divideBoolTag
        (decide (state.query.first = state.query.last) ||
          indexedTransitionRawBool tromino periodicStrip
            state.query.first state.query.last)]
      (baseBoolCost tromino periodicStrip context stateCount state) := by
  have raw :=
    Turing.PartrecToTM2.EvaluatorCodeFits.flatStripBase
      tromino context stateCount state periodicStrip wellFormed
  cases result :
      (decide (state.query.first = state.query.last) ||
        indexedTransitionRawBool tromino periodicStrip
          state.query.first state.query.last) <;>
    simpa [flatProgramList, baseBoolCost, result, divideBoolTag] using raw

def stepSpaceUnit
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (context stateCount : Nat) (state : DivideEvalState) : Nat :=
  encodedListSpace
      (flatProgramList (PeriodicStripFlatEncoding.stripFields periodicStrip)
        context stateCount state) +
    baseBoolCost tromino periodicStrip context stateCount state + 1

def stepCost
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (context stateCount : Nat) (state : DivideEvalState) : Nat :=
  1000000000000000000000000000000 *
    stepSpaceUnit tromino periodicStrip context stateCount state

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem exactStep
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (context stateCount : Nat) (state : FiniteState.DivideEvalState) :
    Turing.PartrecToTM2.EvaluatorCodeFits
        (FiniteState.DivideEvalPartrec.stepCode
          (FlatStripEdgePartrec.baseCode tromino))
        (flatProgramList (PeriodicStripFlatEncoding.stripFields periodicStrip)
          context stateCount state)
        (flatProgramList (PeriodicStripFlatEncoding.stripFields periodicStrip)
          context stateCount
          (FiniteState.divideEvalStep stateCount
            (indexedTransitionRawBool tromino periodicStrip) state))
        (stepCost tromino periodicStrip context stateCount state) := by
  cases state with
  | mk query stack answer =>
    cases query with
    | mk depth first last =>
      let values :=
        flatProgramList (PeriodicStripFlatEncoding.stripFields periodicStrip)
          context stateCount
          { query := { depth := depth, first := first, last := last },
            stack := stack, answer := answer }
      cases answer with
      | none =>
        cases depth with
        | zero =>
          let state : FiniteState.DivideEvalState :=
            { query := { depth := 0, first := first, last := last },
              stack := stack, answer := none }
          have base := baseBool tromino periodicStrip wellFormed context stateCount state
          let baseResult :=
            FiniteState.divideBoolTag
              (decide (first = last) ||
                indexedTransitionRawBool tromino periodicStrip first last)
          let tag := someBoolField values
            (FlatStripEdgePartrec.baseCode tromino) baseResult
            (baseBoolCost tromino periodicStrip context stateCount state)
            (by simpa [values, state, baseResult] using base)
          let fieldFits : List (FieldFit values) :=
            [getField 0 values, getField 1 values, getField 2 values, tag,
              getField 4 values, getField 5 values, getField 6 values]
          have branch := fields values fieldFits (drop 7 values)
          have depthBranch := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.noneDepthSucc)
            (testValue := 0) rfl
            (get 4 values) (by simpa [values, state, fieldFits, tag] using branch)
          have whole := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
            (testValue := 0) rfl
            (get 3 values) depthBranch
          let unit := stepSpaceUnit tromino periodicStrip context stateCount state
          have valuesBound : encodedListSpace values ≤ unit := by
            simp [unit, stepSpaceUnit, values, state]
            omega
          have baseCostBound :
              baseBoolCost tromino periodicStrip context stateCount state ≤ unit := by
            simp [unit, stepSpaceUnit]
            omega
          have unitPositive : 1 ≤ unit := by
            simp [unit, stepSpaceUnit]
          have baseResultBound : baseResult ≤ 1 := by
            cases result :
                (decide (first = last) ||
                  indexedTransitionRawBool tromino periodicStrip first last) <;>
              simp [baseResult, result, FiniteState.divideBoolTag]
          have tagCostBound : tag.cost ≤ 100000000 * (unit + 1) := by
            simpa [tag, someBoolField] using
              someBoolTagCost_le_budget values baseResult
                (baseBoolCost tromino periodicStrip context stateCount state) unit
                baseResultBound valuesBound baseCostBound unitPositive
          dsimp [tag, someBoolField] at tagCostBound
          have get0 := listCodeGetCost_le_linear 0 values
          have get1 := listCodeGetCost_le_linear 1 values
          have get2 := listCodeGetCost_le_linear 2 values
          have get3 := listCodeGetCost_le_linear 3 values
          have get4 := listCodeGetCost_le_linear 4 values
          have get5 := listCodeGetCost_le_linear 5 values
          have get6 := listCodeGetCost_le_linear 6 values
          have drop7 := dropCost_le_linear 7 values
          have identity := idCost_le_linear values
          have get0Bound : getCost 0 values ≤ 10000 * (unit + 1) :=
            get0.trans (by gcongr)
          have get1Bound : getCost 1 values ≤ 20000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get1.trans (Nat.mul_le_mul_left 20000
                (Nat.add_le_add_right valuesBound 1))
          have get2Bound : getCost 2 values ≤ 30000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get2.trans (Nat.mul_le_mul_left 30000
                (Nat.add_le_add_right valuesBound 1))
          have get3Bound : getCost 3 values ≤ 40000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get3.trans (Nat.mul_le_mul_left 40000
                (Nat.add_le_add_right valuesBound 1))
          have get4Bound : getCost 4 values ≤ 50000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get4.trans (Nat.mul_le_mul_left 50000
                (Nat.add_le_add_right valuesBound 1))
          have get5Bound : getCost 5 values ≤ 60000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get5.trans (Nat.mul_le_mul_left 60000
                (Nat.add_le_add_right valuesBound 1))
          have get6Bound : getCost 6 values ≤ 70000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              get6.trans (Nat.mul_le_mul_left 70000
                (Nat.add_le_add_right valuesBound 1))
          have drop7Bound : dropCost 7 values ≤ 80000 * (unit + 1) := by
            simpa only [Nat.reduceAdd, Nat.reduceMul] using
              drop7.trans (Nat.mul_le_mul_left 80000
                (Nat.add_le_add_right valuesBound 1))
          have identityBound : idCost values ≤ 10 * (unit + 1) :=
            identity.trans (Nat.mul_le_mul_left 10
              (Nat.add_le_add_right valuesBound 1))
          have explicitValuesBound := valuesBound
          have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
          have oneBits : (Computability.encodeNat 1).length = 1 := rfl
          have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
          cases baseAnswer :
              (decide (first = last) ||
                indexedTransitionRawBool tromino periodicStrip first last)
          all_goals
            apply Turing.PartrecToTM2.EvaluatorCodeFits.mono
            · simpa [FiniteState.DivideEvalPartrec.stepCode,
                FiniteState.DivideEvalPartrec.answerNone,
                FiniteState.DivideEvalPartrec.noneDepthZero,
                FiniteState.DivideEvalPartrec.field,
                FiniteState.DivideEvalPartrec.fields,
                flatProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideEvalStep, values, state, fieldFits, tag,
                baseResult, baseAnswer, getField, someBoolField,
                FiniteState.divideBoolTag,
                FiniteState.divideOptionBoolTag] using whole
            · rw [show stepCost tromino periodicStrip context stateCount state =
                  1000000000000000000000000000000 * unit by rfl]
              simp [fieldsCost,
                branchZeroZeroCost, branchZeroTestCost, prependCost,
                baseResult, baseAnswer, values, state,
                getField, someBoolField,
                flatProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideOptionBoolTag,
                FiniteState.divideBoolTag,
                zeroBits, oneBits, twoBits] at tagCostBound get0Bound get1Bound get2Bound get3Bound get4Bound get5Bound get6Bound drop7Bound identityBound explicitValuesBound ⊢
              omega
        | succ depth =>
          cases stateCount with
          | zero =>
            let state : FiniteState.DivideEvalState :=
              { query := { depth := depth + 1, first := first, last := last },
                stack := stack, answer := none }
            let fieldFits : List (FieldFit values) :=
              [getField 0 values, getField 1 values, getField 2 values,
                oneField values, getField 4 values, getField 5 values,
                getField 6 values]
            have countBranch := fields values fieldFits (drop 7 values)
            have depthBranch := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.noneCountSucc)
              (testValue := 0) rfl
              (get 1 values)
              (by simpa [values, state, fieldFits] using countBranch)
            have answerBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneDepthZero
                (FlatStripEdgePartrec.baseCode tromino))
              (testValue := depth + 1)
              (by omega) (get 4 values)
              (by simpa [values, state] using depthBranch)
            have whole := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
              (testValue := 0) rfl
              (get 3 values) answerBranch
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
              FiniteState.DivideEvalPartrec.answerNone,
              FiniteState.DivideEvalPartrec.noneDepthSucc,
              FiniteState.DivideEvalPartrec.noneCountZero,
              FiniteState.DivideEvalPartrec.field,
              FiniteState.DivideEvalPartrec.fields,
              flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideEvalStep, values, state, fieldFits,
              getField, oneField,
              FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip context 0 state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
            have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
            have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
            have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
            have drop7 := dropCost_le_budget 7 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have one := oneCost_le_budget values unit valuesBound
            have tail := listCodeTailCost_le_linear (depth :: values)
            have depthBits := listCodeEncodeNat_length_mono
              (show depth ≤ depth + 1 by omega)
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            rw [show stepCost tromino periodicStrip context 0 state =
                1000000000000000000000000000000 * unit by rfl]
            simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state, fieldFits,
              getField, oneField, flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideOptionBoolTag, zeroBits, oneBits]
              at get0 get1 get2 get3 get4 get5 get6 drop7 identity one tail depthBits explicitValuesBound ⊢
            omega
          | succ middle =>
            let state : FiniteState.DivideEvalState :=
              { query := { depth := depth + 1, first := first, last := last },
                stack := stack, answer := none }
            let fieldFits : List (FieldFit values) :=
              [getField 0 values, getField 1 values, succField 2 values,
                zeroField values, predecessorField 4 values,
                getField 5 values, predecessorField 1 values,
                predecessorField 4 values, getField 5 values,
                getField 6 values, predecessorField 1 values,
                zeroField values, zeroField values]
            have countBranch := fields values fieldFits (drop 7 values)
            have depthBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneCountZero)
              (testValue := middle + 1)
              (by omega) (get 1 values)
              (by simpa [values, state, fieldFits] using countBranch)
            have answerBranch := branchZero_succ
              (whenZero := FiniteState.DivideEvalPartrec.noneDepthZero
                (FlatStripEdgePartrec.baseCode tromino))
              (testValue := depth + 1)
              (by omega) (get 4 values)
              (by simpa [values, state] using depthBranch)
            have whole := branchZero_zero
              (whenSucc := FiniteState.DivideEvalPartrec.answerSome)
              (testValue := 0) rfl
              (get 3 values) answerBranch
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
              FiniteState.DivideEvalPartrec.answerNone,
              FiniteState.DivideEvalPartrec.noneDepthSucc,
              FiniteState.DivideEvalPartrec.noneCountSucc,
              FiniteState.DivideEvalPartrec.field,
              FiniteState.DivideEvalPartrec.predecessorField,
              FiniteState.DivideEvalPartrec.fields,
              flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.DivideFrame.toNatList,
              FiniteState.divideStackToNatList,
              FiniteState.divideEvalStep, values, state, fieldFits,
              getField, succField, zeroField, predecessorField,
              FiniteState.divideBoolTag,
              FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip context (middle + 1) state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
            have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
            have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
            have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
            have drop7 := dropCost_le_budget 7 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have zero := zeroCost_le_budget values unit valuesBound
            have successor := successorFieldCost_le_budget 2 values unit
              (by omega) valuesBound
            have predecessor1 := predecessorFieldCost_le_budget 1 values unit
              (by omega) valuesBound
            have predecessor4 := predecessorFieldCost_le_budget 4 values unit
              (by omega) valuesBound
            have middleTail := listCodeTailCost_le_linear (middle :: values)
            have depthTail := listCodeTailCost_le_linear (depth :: values)
            have middleBits := listCodeEncodeNat_length_mono
              (show middle ≤ middle + 1 by omega)
            have depthBits := listCodeEncodeNat_length_mono
              (show depth ≤ depth + 1 by omega)
            have stackBits := encodeNat_succ_length_le stack.length
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            rw [show stepCost tromino periodicStrip context (middle + 1) state =
                1000000000000000000000000000000 * unit by rfl]
            simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state, fieldFits,
              getField, succField, zeroField, predecessorField,
              flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.DivideFrame.toNatList,
              FiniteState.divideStackToNatList,
              FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
              zeroBits, oneBits]
              at get0 get1 get2 get3 get4 get5 get6 drop7 identity zero successor predecessor1 predecessor4 middleTail depthTail middleBits depthBits stackBits explicitValuesBound ⊢
            omega
      | some answerValue =>
        cases stack with
        | nil =>
          let state : FiniteState.DivideEvalState :=
            { query := { depth := depth, first := first, last := last },
              stack := [], answer := some answerValue }
          have answerTest :
              Turing.PartrecToTM2.EvaluatorCodeFits
                (Turing.ToPartrec.Code.get 3) values
                [FiniteState.divideBoolTag answerValue + 1]
                (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
            cases answerValue <;>
            simpa [values, state, flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideBoolTag,
              FiniteState.divideOptionBoolTag] using
                Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
          have stackBranch := branchZero_zero
            (whenSucc := FiniteState.DivideEvalPartrec.someFrame)
            (testValue := 0) rfl
            (get 2 values) (id values)
          have whole := branchZero_succ
            (whenZero := FiniteState.DivideEvalPartrec.answerNone
              (FlatStripEdgePartrec.baseCode tromino))
            (testValue := FiniteState.divideBoolTag answerValue + 1)
            (by cases answerValue <;> simp [FiniteState.divideBoolTag])
            answerTest
            (by simpa [values, state] using stackBranch)
          cases answerValue
          all_goals
            have wholeFits := (by
              simpa [FiniteState.DivideEvalPartrec.stepCode,
                FiniteState.DivideEvalPartrec.answerSome,
                FiniteState.DivideEvalPartrec.field,
                flatProgramList,
                FiniteState.DivideEvalState.toNatList,
                FiniteState.divideEvalStep, values, state,
                FiniteState.divideBoolTag,
                FiniteState.divideOptionBoolTag] using whole)
            apply wholeFits.mono
            let unit := stepSpaceUnit tromino periodicStrip context stateCount state
            have valuesBound : encodedListSpace values ≤ unit := by
              simp [unit, stepSpaceUnit, values, state]
              omega
            have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
            have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
            have identity := idCost_le_budget values unit valuesBound
            have tail0 := listCodeTailCost_le_linear (0 :: values)
            have tail1 := listCodeTailCost_le_linear (1 :: values)
            have explicitValuesBound := valuesBound
            have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
            have oneBits : (Computability.encodeNat 1).length = 1 := rfl
            have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
            rw [show stepCost tromino periodicStrip context stateCount state =
                1000000000000000000000000000000 * unit by rfl]
            simp [branchZeroZeroCost, branchZeroSuccCost,
              branchZeroTestCost, prependCost, values, state,
              flatProgramList,
              FiniteState.DivideEvalState.toNatList,
              FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
              zeroBits, oneBits, twoBits]
              at get2 get3 identity tail0 tail1 explicitValuesBound ⊢
            omega
        | cons frame rest =>
          cases frame with
          | mk frameDepth frameFirst frameLast middle accumulated leftAnswer =>
            cases leftAnswer with
            | none =>
              let state : FiniteState.DivideEvalState :=
                { query := { depth := depth, first := first, last := last },
                  stack := (⟨frameDepth, frameFirst, frameLast, middle,
                    accumulated, none⟩ : FiniteState.DivideFrame) :: rest,
                  answer := some answerValue }
              let fieldFits : List (FieldFit values) :=
                [getField 0 values, getField 1 values, getField 2 values,
                  zeroField values, getField 7 values, getField 10 values,
                  getField 9 values, getField 7 values, getField 8 values,
                  getField 9 values, getField 10 values, getField 11 values,
                  getField 3 values]
              have answerTest :
                  Turing.PartrecToTM2.EvaluatorCodeFits
                    (Turing.ToPartrec.Code.get 3) values
                    [FiniteState.divideBoolTag answerValue + 1]
                    (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                cases answerValue <;>
                simpa [values, state, flatProgramList,
                  FiniteState.DivideEvalState.toNatList,
                  FiniteState.DivideFrame.toNatList,
                  FiniteState.divideStackToNatList,
                  FiniteState.divideBoolTag,
                  FiniteState.divideOptionBoolTag] using
                    Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
              have leftBranch := fields values fieldFits (drop 13 values)
              have frameBranch := branchZero_zero
                (whenSucc := FiniteState.DivideEvalPartrec.someLeftSome)
                (testValue := 0) rfl
                (get 12 values)
                (by simpa [values, state, fieldFits] using leftBranch)
              have stackBranch := branchZero_succ
                (whenZero := Turing.ToPartrec.Code.id)
                (testValue := rest.length + 1)
                (by omega) (get 2 values)
                (by simpa [values, state] using frameBranch)
              have whole := branchZero_succ
                (whenZero := FiniteState.DivideEvalPartrec.answerNone
                  (FlatStripEdgePartrec.baseCode tromino))
                (testValue := FiniteState.divideBoolTag answerValue + 1)
                (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                answerTest
                (by simpa [values, state] using stackBranch)
              cases answerValue <;> cases accumulated
              all_goals
                have wholeFits := (by
                  simpa [FiniteState.DivideEvalPartrec.stepCode,
                    FiniteState.DivideEvalPartrec.answerSome,
                    FiniteState.DivideEvalPartrec.someFrame,
                    FiniteState.DivideEvalPartrec.someLeftNone,
                    FiniteState.DivideEvalPartrec.field,
                    FiniteState.DivideEvalPartrec.fields,
                    flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideEvalStep, values, state, fieldFits,
                    getField, zeroField,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using whole)
                apply wholeFits.mono
                let unit := stepSpaceUnit tromino periodicStrip context stateCount state
                have valuesBound : encodedListSpace values ≤ unit := by
                  simp [unit, stepSpaceUnit, values, state]
                  omega
                have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                have get7 := getCost_le_budget 7 values unit (by omega) valuesBound
                have get8 := getCost_le_budget 8 values unit (by omega) valuesBound
                have get9 := getCost_le_budget 9 values unit (by omega) valuesBound
                have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                  exact (dropCost_le_linear 13 values).trans (by
                    norm_num
                    gcongr)
                have identity := idCost_le_budget values unit valuesBound
                have zero := zeroCost_le_budget values unit valuesBound
                have restTail := listCodeTailCost_le_linear (rest.length :: values)
                have tail0 := listCodeTailCost_le_linear (0 :: values)
                have tail1 := listCodeTailCost_le_linear (1 :: values)
                have restBits := listCodeEncodeNat_length_mono
                  (show rest.length ≤ rest.length + 1 by omega)
                have explicitValuesBound := valuesBound
                have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                rw [show stepCost tromino periodicStrip context stateCount state =
                    1000000000000000000000000000000 * unit by rfl]
                simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                  branchZeroTestCost, prependCost, values, state, fieldFits,
                  getField, zeroField, flatProgramList,
                  FiniteState.DivideEvalState.toNatList,
                  FiniteState.DivideFrame.toNatList,
                  FiniteState.divideStackToNatList,
                  FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                  zeroBits, oneBits, twoBits]
                  at get0 get1 get2 get3 get7 get8 get9 get10 get11 get12 drop13 identity zero restTail tail0 tail1 restBits explicitValuesBound ⊢
                omega
            | some leftValue =>
              cases middle with
              | zero =>
                let state : FiniteState.DivideEvalState :=
                  { query := { depth := depth, first := first, last := last },
                    stack := (⟨frameDepth, frameFirst, frameLast, 0,
                      accumulated, some leftValue⟩ :
                        FiniteState.DivideFrame) :: rest,
                    answer := some answerValue }
                let leftFit := predecessorField 12 values
                let answerFit := predecessorField 3 values
                let both := boolAnd leftFit.fits answerFit.fits
                let accumulatedFit := boolOr (get 11 values) both
                let rawAccumulatedField : FieldFit values :=
                  { code := FiniteState.DivideEvalPartrec.accumulatedCode,
                    output := if values[11]?.getD 0 = 0 ∧
                        (¬(values[12]?.getD 0).pred = 0 →
                          (values[3]?.getD 0).pred = 0)
                      then 0 else 1,
                    cost := _,
                    fits := by
                      simpa [FiniteState.DivideEvalPartrec.accumulatedCode,
                        FiniteState.DivideEvalPartrec.predecessorField,
                        FiniteState.DivideEvalPartrec.field, leftFit,
                        answerFit, predecessorField] using
                          accumulatedFit }
                let accumulatedField : FieldFit values :=
                  someBoolField values
                    FiniteState.DivideEvalPartrec.accumulatedCode
                    rawAccumulatedField.output rawAccumulatedField.cost
                    rawAccumulatedField.fits
                let fieldFits : List (FieldFit values) :=
                  [getField 0 values, getField 1 values,
                    predecessorField 2 values, accumulatedField,
                    getField 4 values, getField 5 values, getField 6 values]
                have answerTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 3) values
                      [FiniteState.divideBoolTag answerValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                  cases answerValue <;>
                  simpa [values, state, flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
                have leftTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 12) values
                      [FiniteState.divideBoolTag leftValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 12 values) := by
                  cases leftValue <;>
                  simpa [values, state, flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 12 values
                have middleBranch := fields values fieldFits (drop 13 values)
                have leftBranch := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.someLeftNone)
                  (testValue := FiniteState.divideBoolTag leftValue + 1)
                  (by cases leftValue <;> simp [FiniteState.divideBoolTag])
                  leftTest
                  (by
                    have zeroBranch := branchZero_zero
                      (whenSucc :=
                        FiniteState.DivideEvalPartrec.someLeftSomeMiddleSucc)
                      (testValue := 0) rfl
                      (get 10 values)
                      (by simpa [values, state, fieldFits,
                          accumulatedField] using middleBranch)
                    simpa [FiniteState.DivideEvalPartrec.someLeftSome] using
                      zeroBranch)
                have frameBranch := branchZero_succ
                  (whenZero := Turing.ToPartrec.Code.id)
                  (testValue := rest.length + 1)
                  (by omega) (get 2 values)
                  (by simpa [values, state] using leftBranch)
                have whole := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.answerNone
                    (FlatStripEdgePartrec.baseCode tromino))
                  (testValue := FiniteState.divideBoolTag answerValue + 1)
                  (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                    answerTest
                  (by simpa [values, state] using frameBranch)
                cases answerValue <;> cases leftValue <;> cases accumulated
                all_goals
                  have wholeFits := (by
                    simpa [FiniteState.DivideEvalPartrec.stepCode,
                      FiniteState.DivideEvalPartrec.answerSome,
                      FiniteState.DivideEvalPartrec.someFrame,
                      FiniteState.DivideEvalPartrec.someLeftSome,
                      FiniteState.DivideEvalPartrec.someLeftSomeMiddleZero,
                      FiniteState.DivideEvalPartrec.accumulatedCode,
                      FiniteState.DivideEvalPartrec.field,
                      FiniteState.DivideEvalPartrec.predecessorField,
                      FiniteState.DivideEvalPartrec.fields,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideEvalStep, values, state, fieldFits,
                      accumulatedField, rawAccumulatedField, someBoolField,
                      getField, predecessorField,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag] using whole)
                  apply wholeFits.mono
                  let unit := stepSpaceUnit tromino periodicStrip context stateCount state
                  have valuesBound : encodedListSpace values ≤ unit := by
                    simp [unit, stepSpaceUnit, values, state]
                    omega
                  have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                  have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                  have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                  have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                  have get4 := getCost_le_budget 4 values unit (by omega) valuesBound
                  have get5 := getCost_le_budget 5 values unit (by omega) valuesBound
                  have get6 := getCost_le_budget 6 values unit (by omega) valuesBound
                  have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                  have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                  have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                  have pred2 := predecessorFieldCost_le_budget 2 values unit
                    (by omega) valuesBound
                  have pred3 := predecessorFieldCost_le_budget 3 values unit
                    (by omega) valuesBound
                  have pred12 := predecessorFieldCost_le_budget 12 values unit
                    (by omega) valuesBound
                  have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                    exact (dropCost_le_linear 13 values).trans (by
                      norm_num
                      gcongr)
                  have identity := idCost_le_budget values unit valuesBound
                  have leftOutput : (predecessorField 12 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have answerOutput : (predecessorField 3 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have accumulatedOutput : values[11]?.getD 0 ≤ 1 := by
                    simp [values, state, flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag]
                  have rawOutputBound : rawAccumulatedField.output ≤ 1 := by
                    dsimp only [rawAccumulatedField]
                    split <;> omega
                  have rawCost : rawAccumulatedField.cost =
                      boolOrCost values (values[11]?.getD 0)
                        (if (predecessorField 12 values).output = 0 ∨
                            (predecessorField 3 values).output = 0
                          then 0 else 1)
                        (getCost 11 values)
                        (boolAndCost values
                          (predecessorField 12 values).output
                          (predecessorField 3 values).output
                          (predecessorField 12 values).cost
                          (predecessorField 3 values).cost) := by
                    rfl
                  have accumulatedFieldBound :
                      accumulatedField.cost ≤
                        accumulatedTagBudget unit := by
                    change someBoolTagCost values rawAccumulatedField.output
                      rawAccumulatedField.cost ≤ _
                    rw [rawCost]
                    exact accumulatedTagCost_le_budget values
                      rawAccumulatedField.output (values[11]?.getD 0)
                      (predecessorField 12 values).output
                      (predecessorField 3 values).output
                      (getCost 11 values)
                      (predecessorField 12 values).cost
                      (predecessorField 3 values).cost unit
                      rawOutputBound accumulatedOutput leftOutput answerOutput
                      valuesBound get11 pred12 pred3
                  have restTail := listCodeTailCost_le_linear (rest.length :: values)
                  have tail0 := listCodeTailCost_le_linear (0 :: values)
                  have tail1 := listCodeTailCost_le_linear (1 :: values)
                  have restBits := listCodeEncodeNat_length_mono
                    (show rest.length ≤ rest.length + 1 by omega)
                  have explicitValuesBound := valuesBound
                  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                  rw [show stepCost tromino periodicStrip context stateCount state =
                      1000000000000000000000000000000 * unit by rfl]
                  simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                    branchZeroTestCost, prependCost, values, state, fieldFits,
                    accumulatedField, rawAccumulatedField, someBoolField,
                    getField, predecessorField,
                    flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                    zeroBits, oneBits, twoBits]
                    at get0 get1 get2 get3 get4 get5 get6 get10 get11 get12 pred2 pred3 pred12 drop13 identity accumulatedFieldBound restTail tail0 tail1 restBits explicitValuesBound ⊢
                  simp [accumulatedTagBudget, accumulatedRawBudget] at accumulatedFieldBound
                  omega
              | succ previousMiddle =>
                let state : FiniteState.DivideEvalState :=
                  { query := { depth := depth, first := first, last := last },
                    stack := (⟨frameDepth, frameFirst, frameLast,
                      previousMiddle + 1, accumulated, some leftValue⟩ :
                        FiniteState.DivideFrame) :: rest,
                    answer := some answerValue }
                let leftFit := predecessorField 12 values
                let answerFit := predecessorField 3 values
                let both := boolAnd leftFit.fits answerFit.fits
                let accumulatedFit := boolOr (get 11 values) both
                let accumulatedField : FieldFit values :=
                  { code := FiniteState.DivideEvalPartrec.accumulatedCode,
                    output := if values[11]?.getD 0 = 0 ∧
                        (¬(values[12]?.getD 0).pred = 0 →
                          (values[3]?.getD 0).pred = 0)
                      then 0 else 1,
                    cost := _,
                    fits := by
                      simpa [FiniteState.DivideEvalPartrec.accumulatedCode,
                        FiniteState.DivideEvalPartrec.predecessorField,
                        FiniteState.DivideEvalPartrec.field, leftFit,
                        answerFit, predecessorField] using
                          accumulatedFit }
                let fieldFits : List (FieldFit values) :=
                  [getField 0 values, getField 1 values, getField 2 values,
                    zeroField values, getField 7 values, getField 8 values,
                    predecessorField 10 values, getField 7 values,
                    getField 8 values, getField 9 values,
                    predecessorField 10 values, accumulatedField,
                    zeroField values]
                have answerTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 3) values
                      [FiniteState.divideBoolTag answerValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 3 values) := by
                  cases answerValue <;>
                  simpa [values, state, flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 3 values
                have leftTest :
                    Turing.PartrecToTM2.EvaluatorCodeFits
                      (Turing.ToPartrec.Code.get 12) values
                      [FiniteState.divideBoolTag leftValue + 1]
                      (Turing.PartrecToTM2.EvaluatorCodeFits.getCost 12 values) := by
                  cases leftValue <;>
                  simpa [values, state, flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideBoolTag,
                    FiniteState.divideOptionBoolTag] using
                      Turing.PartrecToTM2.EvaluatorCodeFits.get 12 values
                have middleFields := fields values fieldFits (drop 13 values)
                have middleBranch := branchZero_succ
                  (whenZero :=
                    FiniteState.DivideEvalPartrec.someLeftSomeMiddleZero)
                  (testValue := previousMiddle + 1) (by omega)
                  (get 10 values)
                  (by simpa [values, state, fieldFits,
                      accumulatedField] using middleFields)
                have leftBranch := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.someLeftNone)
                  (testValue := FiniteState.divideBoolTag leftValue + 1)
                  (by cases leftValue <;> simp [FiniteState.divideBoolTag])
                  leftTest
                  (by simpa [FiniteState.DivideEvalPartrec.someLeftSome] using
                    middleBranch)
                have frameBranch := branchZero_succ
                  (whenZero := Turing.ToPartrec.Code.id)
                  (testValue := rest.length + 1)
                  (by omega) (get 2 values)
                  (by simpa [values, state] using leftBranch)
                have whole := branchZero_succ
                  (whenZero := FiniteState.DivideEvalPartrec.answerNone
                    (FlatStripEdgePartrec.baseCode tromino))
                  (testValue := FiniteState.divideBoolTag answerValue + 1)
                  (by cases answerValue <;> simp [FiniteState.divideBoolTag])
                  answerTest
                  (by simpa [values, state] using frameBranch)
                cases answerValue <;> cases leftValue <;> cases accumulated
                all_goals
                  have wholeFits := (by
                    simpa [FiniteState.DivideEvalPartrec.stepCode,
                      FiniteState.DivideEvalPartrec.answerSome,
                      FiniteState.DivideEvalPartrec.someFrame,
                      FiniteState.DivideEvalPartrec.someLeftSome,
                      FiniteState.DivideEvalPartrec.someLeftSomeMiddleSucc,
                      FiniteState.DivideEvalPartrec.accumulatedCode,
                      FiniteState.DivideEvalPartrec.field,
                      FiniteState.DivideEvalPartrec.predecessorField,
                      FiniteState.DivideEvalPartrec.fields,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideEvalStep, values, state, fieldFits,
                      accumulatedField, getField, zeroField,
                      predecessorField,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag] using whole)
                  apply wholeFits.mono
                  let unit := stepSpaceUnit tromino periodicStrip context stateCount state
                  have valuesBound : encodedListSpace values ≤ unit := by
                    simp [unit, stepSpaceUnit, values, state]
                    omega
                  have get0 := getCost_le_budget 0 values unit (by omega) valuesBound
                  have get1 := getCost_le_budget 1 values unit (by omega) valuesBound
                  have get2 := getCost_le_budget 2 values unit (by omega) valuesBound
                  have get3 := getCost_le_budget 3 values unit (by omega) valuesBound
                  have get7 := getCost_le_budget 7 values unit (by omega) valuesBound
                  have get8 := getCost_le_budget 8 values unit (by omega) valuesBound
                  have get9 := getCost_le_budget 9 values unit (by omega) valuesBound
                  have get10 := getCost_le_budget 10 values unit (by omega) valuesBound
                  have get11 := getCost_le_budget 11 values unit (by omega) valuesBound
                  have get12 := getCost_le_budget 12 values unit (by omega) valuesBound
                  have pred3 := predecessorFieldCost_le_budget 3 values unit
                    (by omega) valuesBound
                  have pred10 := predecessorFieldCost_le_budget 10 values unit
                    (by omega) valuesBound
                  have pred12 := predecessorFieldCost_le_budget 12 values unit
                    (by omega) valuesBound
                  have drop13 : dropCost 13 values ≤ 140000 * (unit + 1) := by
                    exact (dropCost_le_linear 13 values).trans (by
                      norm_num
                      gcongr)
                  have identity := idCost_le_budget values unit valuesBound
                  have zero := zeroCost_le_budget values unit valuesBound
                  have leftOutput : (predecessorField 12 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have answerOutput : (predecessorField 3 values).output ≤ 1 := by
                    simp [predecessorField, values, state,
                      flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideOptionBoolTag,
                      FiniteState.divideBoolTag]
                  have accumulatedOutput : values[11]?.getD 0 ≤ 1 := by
                    simp [values, state, flatProgramList,
                      FiniteState.DivideEvalState.toNatList,
                      FiniteState.DivideFrame.toNatList,
                      FiniteState.divideStackToNatList,
                      FiniteState.divideBoolTag,
                      FiniteState.divideOptionBoolTag]
                  have accumulatedFieldOutput : accumulatedField.output ≤ 1 := by
                    dsimp only [accumulatedField]
                    split <;> omega
                  have accumulatedFieldCost : accumulatedField.cost =
                      boolOrCost values (values[11]?.getD 0)
                        (if (predecessorField 12 values).output = 0 ∨
                            (predecessorField 3 values).output = 0
                          then 0 else 1)
                        (getCost 11 values)
                        (boolAndCost values
                          (predecessorField 12 values).output
                          (predecessorField 3 values).output
                          (predecessorField 12 values).cost
                          (predecessorField 3 values).cost) := by
                    rfl
                  have accumulatedFieldBound :
                      accumulatedField.cost ≤ accumulatedRawBudget unit := by
                    rw [accumulatedFieldCost]
                    exact accumulatedRawCost_le_budget values
                      (values[11]?.getD 0)
                      (predecessorField 12 values).output
                      (predecessorField 3 values).output
                      (getCost 11 values)
                      (predecessorField 12 values).cost
                      (predecessorField 3 values).cost unit
                      accumulatedOutput leftOutput answerOutput valuesBound
                      get11 pred12 pred3
                  have middleTail := listCodeTailCost_le_linear
                    (previousMiddle :: values)
                  have restTail := listCodeTailCost_le_linear (rest.length :: values)
                  have tail0 := listCodeTailCost_le_linear (0 :: values)
                  have tail1 := listCodeTailCost_le_linear (1 :: values)
                  have middleBits := listCodeEncodeNat_length_mono
                    (show previousMiddle ≤ previousMiddle + 1 by omega)
                  have restBits := listCodeEncodeNat_length_mono
                    (show rest.length ≤ rest.length + 1 by omega)
                  have explicitValuesBound := valuesBound
                  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
                  have oneBits : (Computability.encodeNat 1).length = 1 := rfl
                  have twoBits : (Computability.encodeNat 2).length = 2 := by native_decide
                  rw [show stepCost tromino periodicStrip context stateCount state =
                      1000000000000000000000000000000 * unit by rfl]
                  simp [fieldsCost, branchZeroZeroCost, branchZeroSuccCost,
                    branchZeroTestCost, prependCost, values, state, fieldFits,
                    accumulatedField, getField, zeroField, predecessorField,
                    flatProgramList,
                    FiniteState.DivideEvalState.toNatList,
                    FiniteState.DivideFrame.toNatList,
                    FiniteState.divideStackToNatList,
                    FiniteState.divideOptionBoolTag, FiniteState.divideBoolTag,
                    zeroBits, oneBits, twoBits]
                    at get0 get1 get2 get3 get7 get8 get9 get10 get11 get12 pred3 pred10 pred12 drop13 identity zero accumulatedFieldBound middleTail restTail tail0 tail1 middleBits restBits explicitValuesBound ⊢
                  simp [accumulatedRawBudget] at accumulatedFieldBound
                  omega


end FlatStripSavitchStep
end FiniteState
end LeanTrominoes
