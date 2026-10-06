/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.DirectedClauseProfileCheck

namespace LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering
open UnaryProgramClauseProfile

/-- Enumerate directions and the final slot after fixing the second literal. -/
def secondDirectedProfileCheck (test : DirectedClauseProfile → Bool)
    (first : LiteralProfile) (direction : AxisDirection) (second : LiteralProfile) : Bool :=
  test (.unary first direction) &&
    finiteAll fun secondDirection : AxisDirection =>
      test (.binary first direction second secondDirection) &&
        finiteAll fun third : LiteralProfile × AxisDirection =>
          test (.ternary first direction second secondDirection third.1 third.2)

/-- The second-literal subchecks cover a complete first-slot certificate. -/
theorem firstDirectedProfileCheck_of_second (test : DirectedClauseProfile → Bool)
    (first : LiteralProfile) (direction : AxisDirection)
    (checks : ∀ second, secondDirectedProfileCheck test first direction second = true) :
    firstDirectedProfileCheck test first direction = true := by
  simp only [firstDirectedProfileCheck, secondDirectedProfileCheck,
    Bool.and_eq_true, finiteAll_eq_true] at checks ⊢
  exact ⟨(checks ⟨false, false⟩).1,
    fun second => (checks second.1).2 second.2⟩

end LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering
