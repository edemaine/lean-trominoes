/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecDivision
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecPackedCenterLoop
import LeanTrominoes.PartrecPackedNormalizationAll
import LeanTrominoes.PartrecPackedOverlapLoop

/-!
# Complete packed frontier transition program

This file composes the executable packed normalization, center-validity, phase
advance, and four-column overlap predicates.  The common input layout is

`[period, currentPhase, motifCode, currentWord, nextPhase, nextWord]`.
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

/-- The six native fields used by the packed transition evaluator. -/
def packedTransitionInput
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) : List Nat :=
  [periodicStrip.period, current.phase,
    Encodable.encode periodicStrip.motif, current.assignmentWord,
    next.phase, next.assignmentWord]

/-- Project the current state into the common four-field packed-predicate
layout. -/
def packedTransitionCurrentArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) (get 3)

@[simp]
theorem packedTransitionCurrentArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionCurrentArgumentsCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [periodicStrip.period, current.phase,
        Encodable.encode periodicStrip.motif,
        current.assignmentWord] := by
  simp [packedTransitionCurrentArgumentsCode,
    packedTransitionInput]

/-- Project the motif and two assignment words into the overlap evaluator's
three-field input. -/
def packedTransitionOverlapArgumentsCode : Code :=
  prepend (get 2) <| prepend (get 3) (get 5)

@[simp]
theorem packedTransitionOverlapArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionOverlapArgumentsCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord] := by
  simp [packedTransitionOverlapArgumentsCode,
    packedTransitionInput]

/-- Form `[currentPhase + 1, period]` for quotient/remainder division. -/
def packedTransitionPhaseDivisionArgumentsCode : Code :=
  prepend (succ.comp (get 1)) (get 0)

@[simp]
theorem packedTransitionPhaseDivisionArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseDivisionArgumentsCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [current.phase + 1, periodicStrip.period] := by
  simp [packedTransitionPhaseDivisionArgumentsCode,
    packedTransitionInput]

/-- Compute `(currentPhase + 1) % period`. -/
def packedTransitionPhaseRemainderCode : Code :=
  (get 1).comp
    (divisionCode.comp packedTransitionPhaseDivisionArgumentsCode)

@[simp]
theorem packedTransitionPhaseRemainderCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseRemainderCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [(current.phase + 1) % periodicStrip.period] := by
  have arguments := packedTransitionPhaseDivisionArgumentsCode_eval
    periodicStrip current next
  have divided :=
    (comp_eval_pure divisionCode
      packedTransitionPhaseDivisionArgumentsCode
      (packedTransitionInput periodicStrip current next)
      [current.phase + 1, periodicStrip.period] arguments).trans
      (divisionCode_eval (current.phase + 1) periodicStrip.period)
  have projected :=
    comp_eval_pure (get 1)
      (divisionCode.comp packedTransitionPhaseDivisionArgumentsCode)
      (packedTransitionInput periodicStrip current next)
      [(current.phase + 1) / periodicStrip.period,
        (current.phase + 1) % periodicStrip.period] divided
  simpa [packedTransitionPhaseRemainderCode] using projected

/-- Form `[nextPhase, (currentPhase + 1) % period]`. -/
def packedTransitionPhaseEqualityArgumentsCode : Code :=
  prepend (get 4) packedTransitionPhaseRemainderCode

@[simp]
theorem packedTransitionPhaseEqualityArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseEqualityArgumentsCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [next.phase,
        (current.phase + 1) % periodicStrip.period] := by
  rw [packedTransitionPhaseEqualityArgumentsCode,
    prepend_eval_eq,
    packedTransitionPhaseRemainderCode_eval]
  simp [packedTransitionInput]

/-- Check the cyclic phase advance between consecutive packed states. -/
def packedTransitionPhaseCode : Code :=
  natEqCode.comp packedTransitionPhaseEqualityArgumentsCode

@[simp]
theorem packedTransitionPhaseCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionPhaseCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [(decide
        (next.phase =
          (current.phase + 1) % periodicStrip.period)).toNat] := by
  have arguments := packedTransitionPhaseEqualityArgumentsCode_eval
    periodicStrip current next
  have compared :=
    (comp_eval_pure natEqCode
      packedTransitionPhaseEqualityArgumentsCode
      (packedTransitionInput periodicStrip current next)
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
  simpa [packedTransitionPhaseCode] using compared

/-- Run complete normalization on the current-state projection. -/
def packedTransitionNormalizationCode : Code :=
  packedNormalizationAllCode.comp packedTransitionCurrentArgumentsCode

@[simp]
theorem packedTransitionNormalizationCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionNormalizationCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [(current.isNormalizedBool periodicStrip).toNat] := by
  simpa [packedTransitionNormalizationCode] using
    (comp_eval_pure packedNormalizationAllCode
      packedTransitionCurrentArgumentsCode
      (packedTransitionInput periodicStrip current next)
      [periodicStrip.period, current.phase,
        Encodable.encode periodicStrip.motif,
        current.assignmentWord]
      (packedTransitionCurrentArgumentsCode_eval
        periodicStrip current next)).trans
      (packedNormalizationAllCode_eval periodicStrip current)

/-- Run complete center validity on the current-state projection. -/
def packedTransitionCenterCode (tromino : Tromino) : Code :=
  (packedCenterValidCode tromino).comp
    packedTransitionCurrentArgumentsCode

@[simp]
theorem packedTransitionCenterCode_eval
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (packedTransitionCenterCode tromino).eval
        (packedTransitionInput periodicStrip current next) =
      pure [(current.isCenterValidBool
        tromino periodicStrip).toNat] := by
  simpa [packedTransitionCenterCode] using
    (comp_eval_pure (packedCenterValidCode tromino)
      packedTransitionCurrentArgumentsCode
      (packedTransitionInput periodicStrip current next)
      [periodicStrip.period, current.phase,
        Encodable.encode periodicStrip.motif,
        current.assignmentWord]
      (packedTransitionCurrentArgumentsCode_eval
        periodicStrip current next)).trans
      (packedCenterValidCode_eval_semantic
        tromino periodicStrip wellFormed current)

/-- Run all four overlap-column scans on their three-field projection. -/
def packedTransitionOverlapColumnsCode : Code :=
  packedOverlapColumnsCode.comp packedTransitionOverlapArgumentsCode

@[simp]
theorem packedTransitionOverlapColumnsCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionOverlapColumnsCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [((List.finRange 4).all fun column =>
        current.overlapsColumnBool periodicStrip next column).toNat] := by
  simpa [packedTransitionOverlapColumnsCode] using
    (comp_eval_pure packedOverlapColumnsCode
      packedTransitionOverlapArgumentsCode
      (packedTransitionInput periodicStrip current next)
      [Encodable.encode periodicStrip.motif,
        current.assignmentWord, next.assignmentWord]
      (packedTransitionOverlapArgumentsCode_eval
        periodicStrip current next)).trans
      (packedOverlapColumnsCode_eval periodicStrip current next)

/-- Complete overlap predicate: cyclic phase advance and all four shared
columns. -/
def packedTransitionOverlapCode : Code :=
  boolAnd packedTransitionPhaseCode
    packedTransitionOverlapColumnsCode

@[simp]
theorem packedTransitionOverlapCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) :
    packedTransitionOverlapCode.eval
        (packedTransitionInput periodicStrip current next) =
      pure [(current.overlapsBool periodicStrip next).toNat] := by
  let phase := decide
    (next.phase = (current.phase + 1) % periodicStrip.period)
  let columns := (List.finRange 4).all fun column =>
    current.overlapsColumnBool periodicStrip next column
  have combined := boolAnd_eval_at_bool
    packedTransitionPhaseCode packedTransitionOverlapColumnsCode
    (packedTransitionInput periodicStrip current next)
    phase columns
    (by simpa [phase] using
      packedTransitionPhaseCode_eval periodicStrip current next)
    (by simpa [columns] using
      (packedTransitionOverlapColumnsCode_eval
        periodicStrip current next))
  change packedTransitionOverlapCode.eval
      (packedTransitionInput periodicStrip current next) =
    pure [(phase && columns).toNat]
  simpa [packedTransitionOverlapCode] using combined

/-- Complete packed raw-transition predicate. -/
def packedTransitionCode (tromino : Tromino) : Code :=
  boolAnd packedTransitionNormalizationCode <|
    boolAnd (packedTransitionCenterCode tromino)
      packedTransitionOverlapCode

@[simp]
theorem packedTransitionCode_eval_semantic
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (packedTransitionCode tromino).eval
        (packedTransitionInput periodicStrip current next) =
      pure [(current.transitionBool
        tromino periodicStrip next).toNat] := by
  let normalized := current.isNormalizedBool periodicStrip
  let center := current.isCenterValidBool tromino periodicStrip
  let overlap := current.overlapsBool periodicStrip next
  have tail := boolAnd_eval_at_bool
    (packedTransitionCenterCode tromino)
    packedTransitionOverlapCode
    (packedTransitionInput periodicStrip current next)
    center overlap
    (by simpa [center] using (packedTransitionCenterCode_eval
      tromino periodicStrip wellFormed current next))
    (by simpa [overlap] using (packedTransitionOverlapCode_eval
      periodicStrip current next))
  have all := boolAnd_eval_at_bool
    packedTransitionNormalizationCode
    (boolAnd (packedTransitionCenterCode tromino)
      packedTransitionOverlapCode)
    (packedTransitionInput periodicStrip current next)
    normalized (center && overlap)
    (by simpa [normalized] using
      (packedTransitionNormalizationCode_eval
        periodicStrip current next))
    tail
  change (packedTransitionCode tromino).eval
      (packedTransitionInput periodicStrip current next) =
    pure [(normalized && center && overlap).toNat]
  simpa [packedTransitionCode, Bool.and_assoc] using all

/-- The executable packed predicate accepts exactly the semantic raw frontier
transitions used by the strip argument. -/
theorem packedTransitionCode_accepts_iff
    (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (current next : PackedWindowState) :
    (packedTransitionCode tromino).eval
        (packedTransitionInput periodicStrip current next) = pure [1] ↔
      (current.toRaw periodicStrip).Transition
        tromino periodicStrip (next.toRaw periodicStrip) := by
  rw [packedTransitionCode_eval_semantic
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
