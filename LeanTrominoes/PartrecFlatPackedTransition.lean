/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDivision
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecFlatPackedCenterLoop
import LeanTrominoes.PartrecFlatPackedNormalizationAll
import LeanTrominoes.PartrecFlatPackedOverlapLoop

/-!
# Complete packed frontier transition on flat motif fields

This file composes flat normalization, center validity, cyclic phase advance,
and four-column overlap.  The common native input is

`[width, period, motif length, current word, current phase,
  next word, next phase, coordinates...]`.
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

private theorem boolAnd_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftCorrect : leftCode.eval values = pure [left.toNat])
    (rightCorrect : rightCode.eval values = pure [right.toNat]) :
    (boolAnd leftCode rightCode).eval values =
      pure [(left && right).toNat] := by
  have combined := boolAnd_eval_at leftCode rightCode values
    left.toNat right.toNat leftCorrect rightCorrect
  cases left <;> cases right <;> simpa using combined

/-- Form `[currentPhase + 1, period]` from the flat transition context. -/
def flatPackedTransitionPhaseDivisionArgumentsCode : Code :=
  prepend (succ.comp (get 4)) (get 1)

@[simp]
theorem flatPackedTransitionPhaseDivisionArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseDivisionArgumentsCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [current.phase + 1, periodicStrip.period] := by
  simp [flatPackedTransitionPhaseDivisionArgumentsCode,
    flatPackedTransitionContext]

/-- Compute `(currentPhase + 1) % period` from flat fields. -/
def flatPackedTransitionPhaseRemainderCode : Code :=
  (get 1).comp
    (divisionCode.comp flatPackedTransitionPhaseDivisionArgumentsCode)

@[simp]
theorem flatPackedTransitionPhaseRemainderCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseRemainderCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(current.phase + 1) % periodicStrip.period] := by
  have arguments := flatPackedTransitionPhaseDivisionArgumentsCode_eval
    periodicStrip current next
  have divided :=
    (comp_eval_pure divisionCode
      flatPackedTransitionPhaseDivisionArgumentsCode
      (flatPackedTransitionContext periodicStrip current next)
      [current.phase + 1, periodicStrip.period] arguments).trans
      (divisionCode_eval (current.phase + 1) periodicStrip.period)
  have projected :=
    comp_eval_pure (get 1)
      (divisionCode.comp flatPackedTransitionPhaseDivisionArgumentsCode)
      (flatPackedTransitionContext periodicStrip current next)
      [(current.phase + 1) / periodicStrip.period,
        (current.phase + 1) % periodicStrip.period] divided
  simpa [flatPackedTransitionPhaseRemainderCode] using projected

/-- Form `[nextPhase, (currentPhase + 1) % period]`. -/
def flatPackedTransitionPhaseEqualityArgumentsCode : Code :=
  prepend (get 6) flatPackedTransitionPhaseRemainderCode

@[simp]
theorem flatPackedTransitionPhaseEqualityArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseEqualityArgumentsCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [next.phase,
        (current.phase + 1) % periodicStrip.period] := by
  rw [flatPackedTransitionPhaseEqualityArgumentsCode,
    prepend_eval_eq,
    flatPackedTransitionPhaseRemainderCode_eval]
  simp [flatPackedTransitionContext]

/-- Check cyclic phase advance between consecutive flat packed states. -/
def flatPackedTransitionPhaseCode : Code :=
  natEqCode.comp flatPackedTransitionPhaseEqualityArgumentsCode

@[simp]
theorem flatPackedTransitionPhaseCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionPhaseCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(decide
        (next.phase =
          (current.phase + 1) % periodicStrip.period)).toNat] := by
  have arguments := flatPackedTransitionPhaseEqualityArgumentsCode_eval
    periodicStrip current next
  have compared :=
    (comp_eval_pure natEqCode
      flatPackedTransitionPhaseEqualityArgumentsCode
      (flatPackedTransitionContext periodicStrip current next)
      [next.phase, (current.phase + 1) % periodicStrip.period]
      arguments).trans
      (natEqCode_eval next.phase
        ((current.phase + 1) % periodicStrip.period))
  have tagEq :
      (decide (next.phase =
        (current.phase + 1) % periodicStrip.period)).toNat =
      if next.phase =
        (current.phase + 1) % periodicStrip.period then 1 else 0 := by
    by_cases advances :
        next.phase =
          (current.phase + 1) % periodicStrip.period <;>
      simp [advances]
  rw [tagEq]
  simpa [flatPackedTransitionPhaseCode] using compared

/-- Complete flat overlap predicate: cyclic phase advance and all four shared
columns. -/
def flatPackedTransitionOverlapCode : Code :=
  boolAnd flatPackedTransitionPhaseCode
    flatPackedOverlapColumnsCode

@[simp]
theorem flatPackedTransitionOverlapCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    flatPackedTransitionOverlapCode.eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(current.overlapsBool periodicStrip next).toNat] := by
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  have combined := boolAnd_eval_at_bool
    flatPackedTransitionPhaseCode flatPackedOverlapColumnsCode
    (flatPackedTransitionContext periodicStrip current next)
    phase columns
    (by simpa [phase] using
      flatPackedTransitionPhaseCode_eval periodicStrip current next)
    (by simpa [columns] using
      flatPackedOverlapColumnsCode_eval periodicStrip current next)
  change flatPackedTransitionOverlapCode.eval
      (flatPackedTransitionContext periodicStrip current next) =
    pure [(phase && columns).toNat]
  simpa [flatPackedTransitionOverlapCode] using combined

/-- Complete packed raw-transition predicate on flat motif fields. -/
def flatPackedTransitionCode (tromino : Tromino) : Code :=
  boolAnd flatPackedNormalizationAllCode <|
    boolAnd (flatPackedCenterValidCode tromino)
      flatPackedTransitionOverlapCode

@[simp]
theorem flatPackedTransitionCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (flatPackedTransitionCode tromino).eval
        (flatPackedTransitionContext periodicStrip current next) =
      pure [(current.transitionBool
        tromino periodicStrip next).toNat] := by
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  have tail := boolAnd_eval_at_bool
    (flatPackedCenterValidCode tromino)
    flatPackedTransitionOverlapCode
    (flatPackedTransitionContext periodicStrip current next)
    center overlap
    (by simpa [center] using
      (flatPackedCenterValidCode_eval_semantic
        tromino periodicStrip wellFormed current next))
    (by simpa [overlap] using
      (flatPackedTransitionOverlapCode_eval
        periodicStrip current next))
  have all := boolAnd_eval_at_bool
    flatPackedNormalizationAllCode
    (boolAnd (flatPackedCenterValidCode tromino)
      flatPackedTransitionOverlapCode)
    (flatPackedTransitionContext periodicStrip current next)
    normalized (center && overlap)
    (by simpa [normalized] using
      (flatPackedNormalizationAllCode_eval
        periodicStrip current next))
    tail
  change (flatPackedTransitionCode tromino).eval
      (flatPackedTransitionContext periodicStrip current next) =
    pure [(normalized && center && overlap).toNat]
  simpa [flatPackedTransitionCode, Bool.and_assoc] using all

/-- The flat executable predicate accepts exactly the semantic raw frontier
transitions used by the strip argument. -/
theorem flatPackedTransitionCode_accepts_iff
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (flatPackedTransitionCode tromino).eval
        (flatPackedTransitionContext periodicStrip current next) = pure [1] ↔
      (current.toRaw periodicStrip).Transition
        tromino periodicStrip (next.toRaw periodicStrip) := by
  rw [flatPackedTransitionCode_eval_semantic
    tromino periodicStrip wellFormed current next]
  let result := current.transitionBool tromino periodicStrip next
  have acceptedIff :
      (pure [result.toNat] : Part (List Nat)) = pure [1] ↔
        result = true := by
    cases result <;> simp
  change pure [result.toNat] = pure [1] ↔ _
  rw [acceptedIff]
  dsimp [result]
  rw [PackedWindowState.transitionBool_toRaw,
    RawWindowState.transitionBool_eq_true_iff]

end Turing.ToPartrec.Code
