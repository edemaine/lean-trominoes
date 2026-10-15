/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.FormulaShape.Route.PeriodicCNFFormulaShapeFigureNineRoutePrefixIndexedProfileCoordinateBlocks

/-! # Source literal indices in indexed Figure 9 coordinate blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineFinalClauseOrdering
open PlanarOneInThreeNoUnitsFigureNine

/-- Every finite routed coordinate records the original literal index selected
by the final within-clause permutation. -/
theorem coordinate_literalIndex_of_mem_expectedSourceClauseIndexedProfileCoordinateBlocks :
    ∀ (profile : DirectedClauseProfile)
      (block : IndexedProfileCoordinateBlock),
      block ∈ expectedSourceClauseIndexedProfileCoordinateBlocks profile →
      ∀ coordinate ∈ block.coordinates,
        coordinate.coordinate.literalIndex =
          (reorderList (List.range block.parent.literalCount)).getD
            coordinate.coordinate.polarity.sourceLiteralIndex 0 := by
  intro profile block blockMember coordinate coordinateMember
  rcases List.mem_iff_getElem.mp blockMember with ⟨index, bound, rfl⟩
  have indexLt : index < (templateDrawingOfClauseProfile
      (clauseProfile (orderedDirectedProfile profile))).formula.length := by
    simpa only [expectedSourceClauseIndexedProfileCoordinateBlocks,
      expectedParentProfileCoordinates,
      expectedSourceClauseHeaderTemplateProfileCoordinateBlocks,
      List.length_zipWith, List.length_map, List.length_zipIdx, min_self] using bound
  unfold expectedSourceClauseIndexedProfileCoordinateBlocks
    expectedParentProfileCoordinates
    expectedSourceClauseHeaderTemplateProfileCoordinateBlocks at coordinateMember ⊢
  dsimp only at coordinateMember ⊢
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_zipIdx]
    at coordinateMember ⊢
  rcases List.mem_map.mp coordinateMember with ⟨polarity, _, rfl⟩
  simp only [ParentProfileCoordinate.literalCount, Nat.zero_add,
    List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some]
  rfl

/-- The literal-index invariant holds in the flattened indexed block schedule
of any direction-aware source. -/
theorem coordinate_literalIndex_of_mem_source_expectedIndexedProfileCoordinateBlocks
    (source : List FormulaShapeDirectionOrdering.Token)
    {block : IndexedProfileCoordinateBlock}
    (blockMember : block ∈
      source.flatMap expectedIndexedProfileCoordinateBlocks)
    {coordinate : HeaderTemplateProfileCoordinate}
    (coordinateMember : coordinate ∈ block.coordinates) :
    coordinate.coordinate.literalIndex =
      (reorderList (List.range block.parent.literalCount)).getD
        coordinate.coordinate.polarity.sourceLiteralIndex 0 := by
  rcases List.mem_flatMap.mp blockMember with
    ⟨token, _tokenMember, blockMember⟩
  cases token with
  | «variable» => simp [expectedIndexedProfileCoordinateBlocks] at blockMember
  | clause profile =>
      exact
        coordinate_literalIndex_of_mem_expectedSourceClauseIndexedProfileCoordinateBlocks
          profile block (by
            simpa only [expectedIndexedProfileCoordinateBlocks] using
              blockMember)
          coordinate coordinateMember

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
