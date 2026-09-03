/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteHeaderPrefixSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceData

/-! # Figure 9 prefix descriptors name their template atoms -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open PlanarOneInThreeNoUnitsFigureNine
open PeriodicCNFStripReduction.HorizontalRoutedRouteHeader

/-- Interpreting a genuine dependent prefix descriptor recovers the atom of
the exact template incidence from which the descriptor was constructed. -/
@[simp] theorem prefixAtom_descriptorAt
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (index : Fin
      (templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.length) :
    prefixAtom (descriptorAt profile index) =
      ((templateDrawingOfClauseProfile
        (clauseProfile profile)).incidenceAt index).literal.1 := by
  unfold descriptorAt
  dsimp only
  split <;> rfl

/-- The whole descriptor block names the template incidences in their exact
clause-major, literal-minor presentation order. -/
theorem clauseDescriptors_map_prefixAtom
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile) :
    (clauseDescriptors profile).map prefixAtom =
      (templateDrawingOfClauseProfile
        (clauseProfile profile)).incidences.map fun incidence =>
          incidence.literal.1 := by
  unfold clauseDescriptors
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro index leftLt rightLt
    simp only [List.getElem_map, List.getElem_finRange]
    exact prefixAtom_descriptorAt profile
      ⟨index, by simpa using leftLt⟩

/-- Every emitted polarity header therefore names the atom of a genuine
incidence in the exact clockwise parent Figure 9 template. -/
theorem exists_prefixAtom_eq_incidenceAt_of_mem_sourceClauseHeaders
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (header : FormulaShapeFigureNinePolarityRouteHeader.Header)
    (headerMember : header ∈
      FormulaShapeFigureNinePolarityRouteHeader.sourceClauseHeaders profile) :
    ∃ index : Fin
        (templateDrawingOfClauseProfile
          (clauseProfile (orderedDirectedProfile profile))).incidences.length,
      prefixAtom header.figurePrefix =
        ((templateDrawingOfClauseProfile
          (clauseProfile (orderedDirectedProfile profile))).incidenceAt
            index).literal.1 := by
  rcases
      FormulaShapeFigureNinePolarityRouteHeader.exists_descriptorAt_eq_figurePrefix_of_mem_sourceClauseHeaders
        profile header headerMember with
    ⟨index, descriptorEq⟩
  refine ⟨index, ?_⟩
  rw [← descriptorEq, prefixAtom_descriptorAt]

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
