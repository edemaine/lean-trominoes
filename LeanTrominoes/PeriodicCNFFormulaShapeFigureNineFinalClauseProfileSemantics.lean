/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfileFigureNineProfileData
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingSemantics

/-! # Logical profiles of the final Figure 9 clause ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open UnaryProgramClauseProfile

/-- The explicit template drawing and the generic logical Figure 9 table
produce the same unit-free literal values in the same clause order.  The
template profiles deliberately clear periodic-anchor bits, so equality of
the complete `LiteralProfile`s would be too strong. -/
theorem figureClauseProfiles_map_literalValues :
    ∀ profile : DirectedClauseProfile,
      ((figureClauseProfiles profile).map fun generated =>
          generated.literals.map LiteralProfile.value) =
        ((ClauseProfileFigureNine.clauseProfiles
          (clauseProfile profile)).map fun generated =>
            generated.literals.map LiteralProfile.value) := by
  native_decide

/-- The arity-indexed final permutation is natural with respect to mapping
the entries of a list. -/
theorem reorderList_map {Source Target : Type*}
    (transform : Source → Target) (values : List Source) :
    reorderList (values.map transform) =
      (reorderList values).map transform := by
  rcases values with _ | ⟨first, values⟩
  · rfl
  rcases values with _ | ⟨second, values⟩
  · rfl
  rcases values with _ | ⟨third, values⟩
  · rfl
  rcases values with _ | ⟨fourth, values⟩ <;> rfl

/-- The final template profile stream carries the generic unit-free Figure 9
literal values after applying `reorderList` inside each generated clause. -/
theorem finalFigureClauseProfiles_map_literalValues
    (profile : DirectedClauseProfile) :
    ((finalFigureClauseProfiles profile).map fun generated =>
        generated.literals.map LiteralProfile.value) =
      ((ClauseProfileFigureNine.clauseProfiles
        (clauseProfile profile)).map fun generated =>
          reorderList
            (generated.literals.map LiteralProfile.value)) := by
  unfold finalFigureClauseProfiles
  rw [List.map_map]
  calc
    (figureClauseProfiles profile).map
          (fun generated =>
            (reorderProfile generated).literals.map LiteralProfile.value) =
        (figureClauseProfiles profile).map
          (fun generated =>
            reorderList
              (generated.literals.map LiteralProfile.value)) := by
      apply List.map_congr_left
      intro generated _generatedMember
      rw [reorderProfile_literals, reorderList_map]
    _ = _ := by
      simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map reorderList)
          (figureClauseProfiles_map_literalValues profile)

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
