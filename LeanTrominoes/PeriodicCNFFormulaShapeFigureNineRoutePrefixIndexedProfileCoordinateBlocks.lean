/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixProfileCoordinateBlocks
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataParentProfileCoordinates

/-! # Parent-indexed blocks of profile-qualified Figure 9 coordinates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open FormulaShapeDirectionOrdering
open PlanarOneInThreeNoUnitsFigureNine

/-- One generated final clause's parent coordinate together with every
profile-qualified routed incidence coordinate emitted by that clause. -/
structure IndexedProfileCoordinateBlock where
  parent : ParentProfileCoordinate
  coordinates : List HeaderTemplateProfileCoordinate
  deriving DecidableEq

/-- Pair the parent-clause coordinate schedule and routed coordinate blocks
of one directed source clause. -/
def expectedSourceClauseIndexedProfileCoordinateBlocks
    (profile : DirectedClauseProfile) :
    List IndexedProfileCoordinateBlock :=
  List.zipWith
    (fun parent coordinates => ⟨parent, coordinates⟩)
    (expectedParentProfileCoordinates
      (clauseProfile (orderedDirectedProfile profile)))
    (expectedSourceClauseHeaderTemplateProfileCoordinateBlocks profile)

/-- The indexed finite blocks project to the exact parent-coordinate
schedule. -/
theorem expectedSourceClauseIndexedProfileCoordinateBlocks_map_parent :
    ∀ profile : DirectedClauseProfile,
      (expectedSourceClauseIndexedProfileCoordinateBlocks profile).map
          IndexedProfileCoordinateBlock.parent =
        expectedParentProfileCoordinates
          (clauseProfile (orderedDirectedProfile profile)) := by
  native_decide

/-- The indexed finite blocks project to the exact routed coordinate block
schedule. -/
theorem expectedSourceClauseIndexedProfileCoordinateBlocks_map_coordinates :
    ∀ profile : DirectedClauseProfile,
      (expectedSourceClauseIndexedProfileCoordinateBlocks profile).map
          IndexedProfileCoordinateBlock.coordinates =
        expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
          profile := by
  native_decide

/-- Every routed coordinate inside an indexed block carries that block's
parent profile and local generated-clause index. -/
theorem coordinate_parent_of_mem_expectedSourceClauseIndexedProfileCoordinateBlocks :
    ∀ (profile : DirectedClauseProfile)
      (block : IndexedProfileCoordinateBlock),
      block ∈ expectedSourceClauseIndexedProfileCoordinateBlocks profile →
      ∀ coordinate ∈ block.coordinates,
        coordinate.profile = block.parent.profile ∧
        coordinate.coordinate.clauseIndex = block.parent.clauseIndex := by
  native_decide

/-- Parent-indexed generated-clause blocks emitted by one source token. -/
def expectedIndexedProfileCoordinateBlocks :
    FormulaShapeDirectionOrdering.Token →
      List IndexedProfileCoordinateBlock
  | .clause profile =>
      expectedSourceClauseIndexedProfileCoordinateBlocks profile
  | .variable => []

/-- The parent-coordinate invariant holds in the flattened block schedule
of any direction-aware source. -/
theorem coordinate_parent_of_mem_source_expectedIndexedProfileCoordinateBlocks
    (source : List FormulaShapeDirectionOrdering.Token)
    {block : IndexedProfileCoordinateBlock}
    (blockMember : block ∈
      source.flatMap expectedIndexedProfileCoordinateBlocks)
    {coordinate : HeaderTemplateProfileCoordinate}
    (coordinateMember : coordinate ∈ block.coordinates) :
    coordinate.profile = block.parent.profile ∧
      coordinate.coordinate.clauseIndex = block.parent.clauseIndex := by
  rcases List.mem_flatMap.mp blockMember with
    ⟨token, _tokenMember, blockMember⟩
  cases token with
  | «variable» => simp [expectedIndexedProfileCoordinateBlocks] at blockMember
  | clause profile =>
      exact
        coordinate_parent_of_mem_expectedSourceClauseIndexedProfileCoordinateBlocks
          profile block (by
            simpa only [expectedIndexedProfileCoordinateBlocks] using
              blockMember)
          coordinate coordinateMember

/-- Projecting coordinates from a complete indexed source schedule recovers
the original generated-clause coordinate blocks. -/
theorem source_flatMap_expectedIndexedProfileCoordinateBlocks_map_coordinates
    (source : List FormulaShapeDirectionOrdering.Token) :
    (source.flatMap expectedIndexedProfileCoordinateBlocks).map
        IndexedProfileCoordinateBlock.coordinates =
      source.flatMap expectedHeaderTemplateProfileCoordinateBlocks := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, List.map_append, List.flatMap_cons]
      cases token with
      | «variable» => simpa [expectedIndexedProfileCoordinateBlocks,
          expectedHeaderTemplateProfileCoordinateBlocks] using induction
      | clause profile =>
          simp only [expectedIndexedProfileCoordinateBlocks,
            expectedHeaderTemplateProfileCoordinateBlocks]
          rw [expectedSourceClauseIndexedProfileCoordinateBlocks_map_coordinates]
          exact congrArg
            (expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
              profile ++ ·) induction

/-- Projecting parents from a complete indexed source schedule recovers the
finite template schedule driven by its clockwise clause profiles. -/
theorem source_flatMap_expectedIndexedProfileCoordinateBlocks_map_parent
    (source : List FormulaShapeDirectionOrdering.Token) :
    (source.flatMap expectedIndexedProfileCoordinateBlocks).map
        IndexedProfileCoordinateBlock.parent =
      (FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape source)).flatMap
          expectedParentProfileCoordinates := by
  rw [FormulaShapeDirectionOrdering.clauseProfiles_shape]
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, List.map_append]
      cases token with
      | «variable» =>
          simpa [expectedIndexedProfileCoordinateBlocks] using induction
      | clause profile =>
          simp only [expectedIndexedProfileCoordinateBlocks,
            List.filterMap_cons, List.flatMap_cons]
          rw [expectedSourceClauseIndexedProfileCoordinateBlocks_map_parent,
            clauseProfile_orderedDirectedProfile,
            induction]

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
