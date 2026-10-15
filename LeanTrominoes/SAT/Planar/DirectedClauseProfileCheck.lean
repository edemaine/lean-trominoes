/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.Computation.Encoding.Finite.FiniteBoolCheck
import LeanTrominoes.SAT.CNF.FormulaShape.PeriodicCNFFormulaShapeDirectionOrderingTokenData

namespace LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering
open UnaryProgramClauseProfile

/-- Enumerate the remaining literal slots after fixing the first literal and direction. -/
def firstDirectedProfileCheck (test : DirectedClauseProfile → Bool)
    (first : LiteralProfile) (direction : AxisDirection) : Bool :=
  test (.unary first direction) &&
    finiteAll fun second : LiteralProfile × AxisDirection =>
      test (.binary first direction second.1 second.2) &&
        finiteAll fun third : LiteralProfile × AxisDirection =>
          test (.ternary first direction second.1 second.2 third.1 third.2)

/-- Certificates for all first slots cover every directed clause profile. -/
theorem firstDirectedProfileCheck_sound (test : DirectedClauseProfile → Bool)
    (checks : ∀ first direction, firstDirectedProfileCheck test first direction = true)
    (profile : DirectedClauseProfile) : test profile = true := by
  cases profile with
  | unary first direction =>
    have checked := checks first direction
    simp only [firstDirectedProfileCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact checked.1
  | binary first direction second secondDirection =>
    have checked := checks first direction
    simp only [firstDirectedProfileCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact (checked.2 ⟨second, secondDirection⟩).1
  | ternary first direction second secondDirection third thirdDirection =>
    have checked := checks first direction
    simp only [firstDirectedProfileCheck, Bool.and_eq_true, finiteAll_eq_true] at checked
    exact ((checked.2 ⟨second, secondDirection⟩).2 ⟨third, thirdDirection⟩)

end LeanTrominoes.PeriodicCNF.FormulaShapeDirectionOrdering
