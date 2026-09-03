/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixProfileCoordinateSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseProfileListSemantics

/-! # Generated-clause blocks of profile-qualified Figure 9 coordinates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineRoutePrefix

open ClauseProfilePolarityRouteOperation
open FormulaShapeDirectionOrdering
open FormulaShapeFigureNineFinalClauseOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open PlanarOneInThreeNoUnitsFigureNine

/-- The profile-qualified header coordinates of one directed source clause,
with the boundary of every generated final Figure 9 clause retained. -/
def expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
    (profile : DirectedClauseProfile) :
    List (List HeaderTemplateProfileCoordinate) :=
  let ordered := orderedDirectedProfile profile
  let drawing := templateDrawingOfClauseProfile (clauseProfile ordered)
  drawing.formula.zipIdx.map fun taggedClause =>
    let generatedProfile := embeddedClauseProfile taggedClause.1
    let sourceOrder :=
      reorderList (List.range taggedClause.1.literals.length)
    (ClauseProfilePolarityRouteOperation.descriptors
      (reorderProfile generatedProfile)).map fun polarity =>
        ⟨clauseProfile ordered,
          ⟨polarity.indexed, taggedClause.2,
            sourceOrder.getD (sourceSlotNat polarity.sourceSlot) 0⟩⟩

/-- Forgetting the generated-clause boundaries recovers the original flat
profile-coordinate schedule. -/
theorem expectedSourceClauseHeaderTemplateProfileCoordinateBlocks_flatten :
    ∀ profile : DirectedClauseProfile,
      (expectedSourceClauseHeaderTemplateProfileCoordinateBlocks
        profile).flatten =
        expectedSourceClauseHeaderTemplateProfileCoordinates profile := by
  native_decide

/-- In every generated-clause block, the coordinate's polarity field is
exactly the polarity descriptor generated from that final clause's literal
values. -/
theorem expectedSourceClauseHeaderTemplateProfileCoordinateBlocks_map_polarity :
    ∀ profile : DirectedClauseProfile,
      (expectedSourceClauseHeaderTemplateProfileCoordinateBlocks profile).map
          (List.map fun coordinate => coordinate.coordinate.polarity) =
        (finalClauseLiteralValueBlock (.clause profile)).map
          indexedDescriptors := by
  native_decide

/-- Generated-clause blocks emitted by one direction-aware source token. -/
def expectedHeaderTemplateProfileCoordinateBlocks :
    FormulaShapeDirectionOrdering.Token →
      List (List HeaderTemplateProfileCoordinate)
  | .clause profile =>
      expectedSourceClauseHeaderTemplateProfileCoordinateBlocks profile
  | .variable => []

/-- Flattening one token's generated-clause blocks recovers its flat header
coordinate block. -/
theorem expectedHeaderTemplateProfileCoordinateBlocks_flatten
    (token : FormulaShapeDirectionOrdering.Token) :
    (expectedHeaderTemplateProfileCoordinateBlocks token).flatten =
      expectedHeaderTemplateProfileCoordinateBlock token := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      exact
        expectedSourceClauseHeaderTemplateProfileCoordinateBlocks_flatten
          profile

/-- Each token's coordinate blocks and final literal-value blocks have the
same per-clause polarity schedules. -/
theorem expectedHeaderTemplateProfileCoordinateBlocks_map_polarity
    (token : FormulaShapeDirectionOrdering.Token) :
    (expectedHeaderTemplateProfileCoordinateBlocks token).map
        (List.map fun coordinate => coordinate.coordinate.polarity) =
      (finalClauseLiteralValueBlock token).map indexedDescriptors := by
  cases token with
  | «variable» => rfl
  | clause profile =>
      exact
        expectedSourceClauseHeaderTemplateProfileCoordinateBlocks_map_polarity
          profile

/-- Flattening the clause-block schedule of a complete source recovers its
flat profile-coordinate schedule. -/
theorem source_flatMap_expectedHeaderTemplateProfileCoordinateBlocks_flatten
    (source : List FormulaShapeDirectionOrdering.Token) :
    (source.flatMap
      expectedHeaderTemplateProfileCoordinateBlocks).flatten =
        source.flatMap expectedHeaderTemplateProfileCoordinateBlock := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      simp only [List.flatMap_cons, List.flatten_append]
      rw [expectedHeaderTemplateProfileCoordinateBlocks_flatten, induction]

/-- The complete generated-clause coordinate blocks project to the same
per-clause polarity schedules as the final Figure 9 literal-value stream. -/
theorem source_flatMap_expectedHeaderTemplateProfileCoordinateBlocks_map_polarity
    (source : List FormulaShapeDirectionOrdering.Token) :
    (source.flatMap expectedHeaderTemplateProfileCoordinateBlocks).map
        (List.map fun coordinate => coordinate.coordinate.polarity) =
      (source.flatMap finalClauseLiteralValueBlock).map
        indexedDescriptors := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [expectedHeaderTemplateProfileCoordinateBlocks_map_polarity,
        induction]

end FormulaShapeFigureNineRoutePrefix
end PeriodicCNF
end LeanTrominoes
