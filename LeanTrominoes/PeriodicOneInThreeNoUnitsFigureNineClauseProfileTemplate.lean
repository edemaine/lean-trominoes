/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineLocalExtendedDirectionCompiler

/-! # Figure 9 templates selected by finite clause profiles -/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

/-- The canonical finite profile of a nonempty width-three positioned clause
selects exactly the same Figure 9 template as the concrete clause. -/
theorem templateDrawingOfClauseProfile_clauseProfile_literalProfiles
    {Variable : Type}
    (clause : PositionedPeriodicClause Variable)
    (nonempty : clause.literals ≠ [])
    (width : clause.literals.length ≤ 3) :
    templateDrawingOfClauseProfile
        (FormulaShapeOfFormula.clauseProfile
          (ClauseProfileOccurrenceSplit.literalProfiles clause.literals)) =
      templateDrawing clause := by
  rcases clause with ⟨position, literals⟩
  dsimp only at nonempty width ⊢
  cases literals with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          simp [FormulaShapeOfFormula.clauseProfile,
            ClauseProfileOccurrenceSplit.literalProfiles,
            templateDrawingOfClauseProfile, templateDrawing]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [FormulaShapeOfFormula.clauseProfile,
                ClauseProfileOccurrenceSplit.literalProfiles,
                templateDrawingOfClauseProfile, templateDrawing]
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [FormulaShapeOfFormula.clauseProfile,
                    ClauseProfileOccurrenceSplit.literalProfiles,
                    templateDrawingOfClauseProfile, templateDrawing]
              | cons fourth rest =>
                  simp only [List.length_cons] at width
                  omega

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
