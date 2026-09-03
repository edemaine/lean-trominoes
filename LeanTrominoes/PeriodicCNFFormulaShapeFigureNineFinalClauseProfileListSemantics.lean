/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseProfileSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingSemantics

/-! # Logical profiles of complete final Figure 9 token streams -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open UnaryProgramClauseProfile

/-- Literal-value clause blocks emitted by the finite final Figure 9 header
source, before terminal-polarity normalization. -/
def finalClauseLiteralValueBlock :
    FormulaShapeDirectionOrdering.Token → List (List Bool)
  | .clause profile =>
      (finalFigureClauseProfiles
        (orderedDirectedProfile profile)).map fun generated =>
          generated.literals.map LiteralProfile.value
  | .variable => []

/-- Expanding a complete directed token stream through the explicit final
Figure 9 tables agrees with the logical Figure 9 profile compiler, followed
by the final within-clause permutation and literal-value projection. -/
theorem source_finalClauseLiteralValues_eq_profiles
    (source : List FormulaShapeDirectionOrdering.Token) :
    source.flatMap finalClauseLiteralValueBlock =
      (ClauseProfileFigureNine.profiles
        (FormulaShape.clauseProfiles
          (FormulaShapeDirectionOrdering.shape source))).map
            fun generated =>
              reorderList
                (generated.literals.map LiteralProfile.value) := by
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape]
  unfold ClauseProfileFigureNine.profiles
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons]
      cases token with
      | «variable» =>
          simpa [finalClauseLiteralValueBlock] using induction
      | clause profile =>
          simp only [finalClauseLiteralValueBlock,
            List.filterMap_cons, List.flatMap_cons, List.map_append]
          rw [finalFigureClauseProfiles_map_literalValues,
            clauseProfile_orderedDirectedProfile]
          exact congrArg
            (fun tail =>
              ((ClauseProfileFigureNine.clauseProfiles
                  profile.orderedProfile).map fun generated =>
                    reorderList
                      (generated.literals.map LiteralProfile.value)) ++ tail)
            induction

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
