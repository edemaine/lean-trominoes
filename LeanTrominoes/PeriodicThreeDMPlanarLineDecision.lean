/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMLineDecision
import LeanTrominoes.PeriodicThreeDMFlatEncoding
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate

/-! # Total decision semantics for supplied-drawing local 1D 3DM

The polynomial-space bound for this native input is a separate obligation.
-/
namespace LeanTrominoes.PeriodicThreeDM

def LocalPlanarLineProblem (input : NormalizationCompiler.Input) : Prop :=
  LocalLineProblem input.problem ∧ FiniteDrawingCertificate.verifies input.problem input.drawing = true

def planarLineCheck (input : NormalizationCompiler.Input) : Bool :=
  lineCheck input.problem && FiniteDrawingCertificate.verifies input.problem input.drawing

theorem planarLineCheck_correct (input : NormalizationCompiler.Input) :
    planarLineCheck input = true ↔ LocalPlanarLineProblem input := by
  rw [planarLineCheck,Bool.and_eq_true,lineCheck_correct]
  rfl

end LeanTrominoes.PeriodicThreeDM
