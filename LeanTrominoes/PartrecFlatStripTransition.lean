/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedTransition
import LeanTrominoes.PartrecFlatStripFrontierContext
import LeanTrominoes.StripFrontierIndexedSearch

/-!
# Flat indexed strip-frontier transition leaf

This module connects the complete flat packed transition predicate to the
suffix-preserving Savitch evaluator.  The leaf reads the two query indices
from the fixed DFS header and the native strip fields from the variable-length
suffix, returning equality or a raw frontier edge at recursion depth zero.
-/

namespace LeanTrominoes.FiniteState

open Turing ToPartrec

namespace FlatStripEdgePartrec

open Code
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Complete flat packed transition on the recovered strip/query context. -/
def transitionCode (tromino : Tromino) : Code :=
  (flatPackedTransitionCode tromino).comp contextCode

@[simp]
theorem transitionCode_eval
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    (transitionCode tromino).eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [(RawWindowState.indexedTransitionRawBool
        tromino periodicStrip state.query.first state.query.last).toNat] := by
  let current := PackedWindowState.ofIndex
    periodicStrip state.query.first
  let next := PackedWindowState.ofIndex
    periodicStrip state.query.last
  have recovered := contextCode_eval
    context stateCount state periodicStrip
  have transition := flatPackedTransitionCode_eval_semantic
    tromino periodicStrip wellFormed current next
  rw [PackedWindowState.indexedTransitionRawBool_eq_packed]
  simpa [transitionCode, flatPackedTransitionContext,
    current, next, PackedWindowState.ofIndex] using
    (comp_eval_pure _ _ _ _ recovered).trans transition

/-- Select the two query indices from the fixed DFS header. -/
def equalityArgumentsCode : Code :=
  prepend (get 5) (get 6)

@[simp]
theorem equalityArgumentsCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    equalityArgumentsCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [state.query.first, state.query.last] := by
  rcases state with ⟨⟨depth, first, last⟩, stack, answer⟩
  simp [equalityArgumentsCode, divideEvalProgramList,
    DivideEvalState.toNatList]

/-- Test equality for the reflexive Savitch base case. -/
def equalityCode : Code :=
  natEqCode.comp equalityArgumentsCode

@[simp]
theorem equalityCode_eval
    (context stateCount : Nat) (state : DivideEvalState)
    (periodicStrip : PeriodicStrip) :
    equalityCode.eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [(decide
        (state.query.first = state.query.last)).toNat] := by
  have arguments := equalityArgumentsCode_eval
    context stateCount state periodicStrip
  have compared :=
    (comp_eval_pure natEqCode equalityArgumentsCode
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip)
      [state.query.first, state.query.last] arguments).trans
      (natEqCode_eval state.query.first state.query.last)
  have tagEq :
      (decide (state.query.first = state.query.last)).toNat =
        if state.query.first = state.query.last then 1 else 0 := by
    by_cases equal : state.query.first = state.query.last <;>
      simp [equal]
  rw [tagEq]
  simpa [equalityCode] using compared

private theorem boolOr_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftCorrect : leftCode.eval values = pure [left.toNat])
    (rightCorrect : rightCode.eval values = pure [right.toNat]) :
    (boolOr leftCode rightCode).eval values =
      pure [(left || right).toNat] := by
  have combined := boolOr_eval_at leftCode rightCode values
    left.toNat right.toNat leftCorrect rightCorrect
  cases left <;> cases right <;> simpa using combined

/-- Explicit reflexive-or-edge leaf for the suffix-preserving Savitch DFS. -/
def baseCode (tromino : Tromino) : Code :=
  boolOr equalityCode (transitionCode tromino)

@[simp]
theorem baseCode_eval
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    (baseCode tromino).eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure [divideBoolTag
        (decide (state.query.first = state.query.last) ||
          RawWindowState.indexedTransitionRawBool
            tromino periodicStrip state.query.first state.query.last)] := by
  let result :=
    decide (state.query.first = state.query.last) ||
      RawWindowState.indexedTransitionRawBool
        tromino periodicStrip state.query.first state.query.last
  have combined := boolOr_eval_at_bool
    equalityCode (transitionCode tromino)
    (divideEvalProgramList context stateCount state ++
      PeriodicStripFlatEncoding.stripFields periodicStrip)
    (decide (state.query.first = state.query.last))
    (RawWindowState.indexedTransitionRawBool
      tromino periodicStrip state.query.first state.query.last)
    (equalityCode_eval context stateCount state periodicStrip)
    (transitionCode_eval tromino context stateCount state
      periodicStrip wellFormed)
  change (baseCode tromino).eval
      (divideEvalProgramList context stateCount state ++
        PeriodicStripFlatEncoding.stripFields periodicStrip) =
    pure [divideBoolTag result]
  cases resultEq : result <;>
    simpa [baseCode, divideBoolTag, result, resultEq] using combined

/-- One compiled Savitch step preserves the native flat strip suffix and uses
the flat frontier relation at depth zero. -/
theorem stepCode_eval
    (tromino : Tromino) (context stateCount : Nat)
    (state : DivideEvalState)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed) :
    (DivideEvalPartrec.stepCode (baseCode tromino)).eval
        (divideEvalProgramList context stateCount state ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) =
      pure
        (divideEvalProgramList context stateCount
          (divideEvalStep stateCount
            (RawWindowState.indexedTransitionRawBool
              tromino periodicStrip) state) ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  exact DivideEvalPartrec.stepCode_eval_suffix
    (baseCode tromino) context stateCount
    (RawWindowState.indexedTransitionRawBool tromino periodicStrip)
    state (PeriodicStripFlatEncoding.stripFields periodicStrip)
    (baseCode_eval tromino context stateCount state
      periodicStrip wellFormed)

/-- The complete flat countdown evaluator preserves the strip suffix and
computes repeated strip-specialized Savitch transitions. -/
theorem flatIterate_eval
    (tromino : Tromino) (context stateCount : Nat)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (steps : Nat) (state : DivideEvalState) :
    (Code.flatIterate
        (DivideEvalPartrec.stepCode (baseCode tromino))).eval
        (steps ::
          (divideEvalProgramList context stateCount state ++
            PeriodicStripFlatEncoding.stripFields periodicStrip)) =
      pure
        (divideEvalProgramList context stateCount
          ((divideEvalStep stateCount
            (RawWindowState.indexedTransitionRawBool
              tromino periodicStrip))^[steps] state) ++
          PeriodicStripFlatEncoding.stripFields periodicStrip) := by
  exact DivideEvalPartrec.flatIterate_stepCode_eval_suffix
    (baseCode tromino) context stateCount
    (RawWindowState.indexedTransitionRawBool tromino periodicStrip)
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
    (fun state => baseCode_eval tromino context stateCount state
      periodicStrip wellFormed)
    steps state

end FlatStripEdgePartrec
end LeanTrominoes.FiniteState
