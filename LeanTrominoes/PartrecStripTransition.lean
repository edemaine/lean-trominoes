/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedTransition
import LeanTrominoes.PartrecStripFrontierContext

/-!
# Explicit indexed strip-frontier transition

This module connects the native packed transition program to the three-field
indexed-search leaf `[encodedStrip, firstIndex, lastIndex]`.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Reorder the seven decoded context fields into the packed transition
layout `[period, currentPhase, motifCode, currentWord, nextPhase, nextWord]`. -/
def stripPackedTransitionArgumentsCode : Code :=
  prepend (get 1) <|
    prepend (get 4) <|
      prepend (get 2) <|
        prepend (get 3) <|
          prepend (get 6) (get 5)

@[simp]
theorem stripPackedTransitionArgumentsCode_eval
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripPackedTransitionArgumentsCode.eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif,
          first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period] =
      pure [periodicStrip.period, first % periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        last % periodicStrip.period,
        last / periodicStrip.period] := by
  simp [stripPackedTransitionArgumentsCode]

/-- Packed transition evaluated on an already decoded seven-field context. -/
def stripPackedTransitionCode (tromino : Tromino) : Code :=
  (packedTransitionCode tromino).comp
    stripPackedTransitionArgumentsCode

@[simp]
theorem stripPackedTransitionCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    (stripPackedTransitionCode tromino).eval
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif,
          first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period] =
      pure [((PeriodicStrip.PackedWindowState.ofIndex
          periodicStrip first).transitionBool tromino periodicStrip
        (PeriodicStrip.PackedWindowState.ofIndex
          periodicStrip last)).toNat] := by
  let current :=
    PeriodicStrip.PackedWindowState.ofIndex periodicStrip first
  let next :=
    PeriodicStrip.PackedWindowState.ofIndex periodicStrip last
  have arguments := stripPackedTransitionArgumentsCode_eval
    periodicStrip first last
  have run := packedTransitionCode_eval_semantic
    tromino periodicStrip wellFormed current next
  simpa [stripPackedTransitionCode,
    packedTransitionInput, current, next,
    PeriodicStrip.PackedWindowState.ofIndex] using
    (comp_eval_pure _ _ _ _ arguments).trans run

/-- Complete explicit indexed edge predicate. -/
def stripTransitionCode (tromino : Tromino) : Code :=
  (stripPackedTransitionCode tromino).comp stripFrontierContextCode

@[simp]
theorem stripTransitionCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    (stripTransitionCode tromino).eval
        [Encodable.encode periodicStrip, first, last] =
      pure [(PeriodicStrip.RawWindowState.indexedTransitionRawBool
        tromino periodicStrip first last).toNat] := by
  have context := stripFrontierContextCode_eval
    periodicStrip first last
  have transition := stripPackedTransitionCode_eval
    tromino periodicStrip wellFormed first last
  rw [PeriodicStrip.PackedWindowState.indexedTransitionRawBool_eq_packed]
  simpa [stripTransitionCode] using
    (comp_eval_pure _ _ _ _ context).trans transition

/-- Select the two search indices for the reflexive Savitch base case. -/
def stripTransitionEqualityArgumentsCode : Code :=
  prepend (get 1) (get 2)

@[simp]
theorem stripTransitionEqualityArgumentsCode_eval
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripTransitionEqualityArgumentsCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure [first, last] := by
  simp [stripTransitionEqualityArgumentsCode]

/-- Test equality of the two indexed frontier states. -/
def stripTransitionEqualityCode : Code :=
  natEqCode.comp stripTransitionEqualityArgumentsCode

@[simp]
theorem stripTransitionEqualityCode_eval
    (periodicStrip : PeriodicStrip) (first last : Nat) :
    stripTransitionEqualityCode.eval
        [Encodable.encode periodicStrip, first, last] =
      pure [(decide (first = last)).toNat] := by
  have arguments := stripTransitionEqualityArgumentsCode_eval
    periodicStrip first last
  have compared :=
    (comp_eval_pure natEqCode stripTransitionEqualityArgumentsCode
      [Encodable.encode periodicStrip, first, last]
      [first, last] arguments).trans (natEqCode_eval first last)
  have tagEq :
      (decide (first = last)).toNat =
        if first = last then 1 else 0 := by
    by_cases equal : first = last <;> simp [equal]
  rw [tagEq]
  simpa [stripTransitionEqualityCode] using compared

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

/-- Explicit reflexive-or-edge predicate used at Savitch recursion depth
zero. -/
def stripBaseTransitionCode (tromino : Tromino) : Code :=
  boolOr stripTransitionEqualityCode (stripTransitionCode tromino)

@[simp]
theorem stripBaseTransitionCode_eval
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (first last : Nat) :
    (stripBaseTransitionCode tromino).eval
        [Encodable.encode periodicStrip, first, last] =
      pure [((decide (first = last)) ||
        PeriodicStrip.RawWindowState.indexedTransitionRawBool
          tromino periodicStrip first last).toNat] := by
  exact boolOr_eval_at_bool
    stripTransitionEqualityCode (stripTransitionCode tromino)
    [Encodable.encode periodicStrip, first, last]
    (decide (first = last))
    (PeriodicStrip.RawWindowState.indexedTransitionRawBool
      tromino periodicStrip first last)
    (stripTransitionEqualityCode_eval periodicStrip first last)
    (stripTransitionCode_eval
      tromino periodicStrip wellFormed first last)

end Turing.ToPartrec.Code
