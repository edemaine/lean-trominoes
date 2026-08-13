/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatStripFrontierContextSpace
import LeanTrominoes.PartrecFlatPackedTransitionSpace
import LeanTrominoes.PartrecFlatStripTransition
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecBooleanSpace

/-!
# Evaluator-space certificate for the recovered flat strip edge

This module composes the bounded seven-field context adapter with the complete
bounded packed transition.  It also fits and bounds the query-index equality
test and their reflexive disjunction, yielding the depth-zero oracle consumed
by suffix-preserving Savitch reachability.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.FiniteState
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatStripTransitionCost
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip) : Nat :=
  let current := PackedWindowState.ofIndex periodicStrip state.query.first
  let next := PackedWindowState.ofIndex periodicStrip state.query.last
  flatPackedTransitionCost tromino periodicStrip current next +
    flatStripContextCost context stateCount state periodicStrip

/-- Exact fitted certificate for the recovered flat indexed strip edge. -/
theorem flatStripTransition
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    EvaluatorCodeFits (FlatStripEdgePartrec.transitionCode tromino)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(RawWindowState.indexedTransitionRawBool tromino periodicStrip
        state.query.first state.query.last).toNat]
      (flatStripTransitionCost
        tromino context stateCount state periodicStrip) := by
  let current := PackedWindowState.ofIndex periodicStrip state.query.first
  let next := PackedWindowState.ofIndex periodicStrip state.query.last
  have result := comp
    (flatPackedTransition tromino periodicStrip wellFormed current next)
    (flatStripContext context stateCount state periodicStrip)
  rw [PackedWindowState.indexedTransitionRawBool_eq_packed]
  simpa [FlatStripEdgePartrec.transitionCode, flatStripTransitionCost,
    current, next, PackedWindowState.ofIndex,
    Code.flatPackedTransitionContext] using result

/-- Native polynomial envelope for the recovered indexed edge. -/
def flatStripTransitionSpaceBound
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip) : Nat :=
  let current := PackedWindowState.ofIndex periodicStrip state.query.first
  let next := PackedWindowState.ofIndex periodicStrip state.query.last
  flatPackedTransitionSpaceBound periodicStrip current next +
    flatStripContextSpaceBound context stateCount state periodicStrip

theorem flatStripTransitionCost_le_bound
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    flatStripTransitionCost tromino context stateCount state periodicStrip ≤
      flatStripTransitionSpaceBound
        tromino context stateCount state periodicStrip := by
  let current := PackedWindowState.ofIndex periodicStrip state.query.first
  let next := PackedWindowState.ofIndex periodicStrip state.query.last
  have transition := flatPackedTransitionCost_le_bound
    tromino periodicStrip wellFormed current next
  have transition' : flatPackedTransitionCost tromino periodicStrip
      (PackedWindowState.ofIndex periodicStrip state.query.first)
      (PackedWindowState.ofIndex periodicStrip state.query.last) ≤
    flatPackedTransitionSpaceBound periodicStrip
      (PackedWindowState.ofIndex periodicStrip state.query.first)
      (PackedWindowState.ofIndex periodicStrip state.query.last) := by
    simpa [current, next] using transition
  have recovered := flatStripContextCost_le_bound
    context stateCount state periodicStrip
  simp only [flatStripTransitionCost, flatStripTransitionSpaceBound]
  omega

theorem flatStripTransitionBounded
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    EvaluatorCodeFits (FlatStripEdgePartrec.transitionCode tromino)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(RawWindowState.indexedTransitionRawBool tromino periodicStrip
        state.query.first state.query.last).toNat]
      (flatStripTransitionSpaceBound
        tromino context stateCount state periodicStrip) :=
  (flatStripTransition tromino context stateCount state periodicStrip
    wellFormed).mono
      (flatStripTransitionCost_le_bound tromino context stateCount state
        periodicStrip wellFormed)

def flatStripEqualityArgumentsCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  flatStripPairArgumentsTailCost context stateCount state periodicStrip

theorem flatStripEqualityArguments
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.equalityArgumentsCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [state.query.first, state.query.last]
      (flatStripEqualityArgumentsCost
        context stateCount state periodicStrip) := by
  simpa [FlatStripEdgePartrec.equalityArgumentsCode,
    flatStripEqualityArgumentsCost] using
    flatStripPairArgumentsTail context stateCount state periodicStrip

def flatStripEqualityCost
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  natEqCost state.query.first state.query.last +
    flatStripEqualityArgumentsCost context stateCount state periodicStrip

theorem flatStripEquality
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.equalityCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (state.query.first = state.query.last)).toNat]
      (flatStripEqualityCost context stateCount state periodicStrip) := by
  have result := comp (natEq state.query.first state.query.last)
    (flatStripEqualityArguments context stateCount state periodicStrip)
  have tagEq :
      (decide (state.query.first = state.query.last)).toNat =
        if state.query.first = state.query.last then 1 else 0 := by
    by_cases equal : state.query.first = state.query.last <;> simp [equal]
  rw [tagEq]
  simpa [FlatStripEdgePartrec.equalityCode,
    flatStripEqualityCost] using result

/-- Polynomial native-field bound for query-index equality. -/
def flatStripEqualitySpaceBound
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) : Nat :=
  10000000000 *
      (encodedListSpace
        [2 * (state.query.first + state.query.last) + 4] + 1) +
    flatStripContextBaseSpaceBound context stateCount state periodicStrip

theorem flatStripEqualityCost_le_bound
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    flatStripEqualityCost context stateCount state periodicStrip ≤
      flatStripEqualitySpaceBound
        context stateCount state periodicStrip := by
  have equality := natEqCost_le_linear state.query.first state.query.last
  have arguments := flatStripPairArgumentsTailCost_le_base
    context stateCount state periodicStrip
  simp only [flatStripEqualityCost, flatStripEqualityArgumentsCost,
    flatStripEqualitySpaceBound]
  omega

theorem flatStripEqualityBounded
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits FlatStripEdgePartrec.equalityCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [(decide (state.query.first = state.query.last)).toNat]
      (flatStripEqualitySpaceBound context stateCount state periodicStrip) :=
  (flatStripEquality context stateCount state periodicStrip).mono
    (flatStripEqualityCost_le_bound context stateCount state periodicStrip)

private theorem boolOr_fit_bool
    {leftCode rightCode : Code} {values : List Nat}
    {leftCost rightCost : Nat}
    (left right : Bool)
    (leftFit : EvaluatorCodeFits leftCode values [left.toNat] leftCost)
    (rightFit : EvaluatorCodeFits rightCode values [right.toNat] rightCost) :
    EvaluatorCodeFits (Code.boolOr leftCode rightCode) values
      [(left || right).toNat]
      (boolOrCost values left.toNat right.toNat leftCost rightCost) := by
  have combined := boolOr leftFit rightFit
  cases left <;> cases right <;> simpa using combined

def flatStripBaseCost
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip) : Nat :=
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let equal := decide (state.query.first = state.query.last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip state.query.first state.query.last
  boolOrCost values equal.toNat edge.toNat
    (flatStripEqualityCost context stateCount state periodicStrip)
    (flatStripTransitionCost tromino context stateCount state periodicStrip)

/-- Exact fitted certificate for the depth-zero reflexive-or-edge oracle. -/
theorem flatStripBase
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    EvaluatorCodeFits (FlatStripEdgePartrec.baseCode tromino)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [((decide (state.query.first = state.query.last)) ||
        RawWindowState.indexedTransitionRawBool tromino periodicStrip
          state.query.first state.query.last).toNat]
      (flatStripBaseCost
        tromino context stateCount state periodicStrip) := by
  let equal := decide (state.query.first = state.query.last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip state.query.first state.query.last
  have result := boolOr_fit_bool equal edge
    (by
      simpa [equal] using
        (flatStripEquality context stateCount state periodicStrip))
    (by
      simpa [edge] using
        (flatStripTransition tromino context stateCount state periodicStrip
          wellFormed))
  simpa [FlatStripEdgePartrec.baseCode, flatStripBaseCost,
    equal, edge] using result

/-- Common budget for the equality and edge programs plus the Boolean
adapter's shared input and successor-head footprints. -/
def flatStripBaseComponentSpaceBound
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip) : Nat :=
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  flatStripEqualitySpaceBound context stateCount state periodicStrip +
    flatStripTransitionSpaceBound tromino context stateCount state periodicStrip +
    encodedListSpace values + encodedListSpace [values.headI + 1] + 10

/-- Polynomial native-field envelope for the complete depth-zero oracle. -/
def flatStripBaseSpaceBound
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip) : Nat :=
  1000 * (flatStripBaseComponentSpaceBound
    tromino context stateCount state periodicStrip + 1)

set_option maxHeartbeats 800000 in
theorem flatStripBaseCost_le_bound
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    flatStripBaseCost tromino context stateCount state periodicStrip ≤
      flatStripBaseSpaceBound
        tromino context stateCount state periodicStrip := by
  let values := divideEvalProgramList context stateCount state ++
    PeriodicStripFlatEncoding.stripFields periodicStrip
  let equal := decide (state.query.first = state.query.last)
  let edge := RawWindowState.indexedTransitionRawBool
    tromino periodicStrip state.query.first state.query.last
  let budget := flatStripBaseComponentSpaceBound
    tromino context stateCount state periodicStrip
  have equalTag : equal.toNat ≤ 1 := Bool.toNat_le equal
  have edgeTag : edge.toNat ≤ 1 := Bool.toNat_le edge
  have valuesBound : encodedListSpace values ≤ budget := by
    simp [budget, flatStripBaseComponentSpaceBound, values]
    omega
  have headBound :
      (Computability.encodeNat values.headI).length ≤ budget := by
    have raw := listCodeEncodedListSpace_singleton_headI_le values
    have room : encodedListSpace values + 1 ≤ budget := by
      simp [budget, flatStripBaseComponentSpaceBound, values]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at raw
    omega
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    have room : encodedListSpace [values.headI + 1] ≤ budget := by
      simp [budget, flatStripBaseComponentSpaceBound, values]
      omega
    simp only [encodedListSpace_cons, encodedListSpace_nil] at room
    omega
  have equalityCost := flatStripEqualityCost_le_bound
    context stateCount state periodicStrip
  have transitionCost := flatStripTransitionCost_le_bound
    tromino context stateCount state periodicStrip wellFormed
  have equalityBound : flatStripEqualityCost
      context stateCount state periodicStrip ≤ budget := by
    simp only [budget, flatStripBaseComponentSpaceBound]
    omega
  have transitionBound : flatStripTransitionCost
      tromino context stateCount state periodicStrip ≤ budget := by
    simp only [budget, flatStripBaseComponentSpaceBound]
    omega
  have positive : 1 ≤ budget := by
    simp [budget, flatStripBaseComponentSpaceBound]
  have bound := boolOrCost_le_budget values equal.toNat edge.toNat
    (flatStripEqualityCost context stateCount state periodicStrip)
    (flatStripTransitionCost tromino context stateCount state periodicStrip)
    budget equalTag edgeTag valuesBound headBound headSuccessorBound
    equalityBound transitionBound positive
  simpa [flatStripBaseCost, flatStripBaseSpaceBound,
    values, equal, edge, budget] using bound

theorem flatStripBaseBounded
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    EvaluatorCodeFits (FlatStripEdgePartrec.baseCode tromino)
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [((decide (state.query.first = state.query.last)) ||
        RawWindowState.indexedTransitionRawBool tromino periodicStrip
          state.query.first state.query.last).toNat]
      (flatStripBaseSpaceBound
        tromino context stateCount state periodicStrip) :=
  (flatStripBase tromino context stateCount state periodicStrip
    wellFormed).mono
      (flatStripBaseCost_le_bound tromino context stateCount state
        periodicStrip wellFormed)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
