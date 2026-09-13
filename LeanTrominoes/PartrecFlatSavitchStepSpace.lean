/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecGenericSavitchStepSpace

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
  exact GenericSavitchStep.exactStep
    (PeriodicStripFlatEncoding.stripFields periodicStrip)
    (FlatStripEdgePartrec.baseCode tromino)
    (indexedTransitionRawBool tromino periodicStrip)
    (baseBoolCost tromino periodicStrip)
    (baseBool tromino periodicStrip wellFormed)
    context stateCount state


end FlatStripSavitchStep
end FiniteState
end LeanTrominoes
