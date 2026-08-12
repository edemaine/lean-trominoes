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

end Turing.ToPartrec.Code
