/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCanonical
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixIndexedProfileCoordinateBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineDirectionExact
import LeanTrominoes.PositionedPeriodicCNFFormulaShapeProfiles

/-! # Retained Figure 9 indexed profile-coordinate blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedFigureNineDirection

open ClauseProfileOccurrenceSplit
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeOfFormula
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine
open UnaryProgramClauseProfile

/-- The clockwise profiles in the retained direction descriptor stream are
exactly the canonical profiles of the concrete clearance clauses. -/
theorem clauseProfiles_shape_descriptors_eq_clearance
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    FormulaShape.clauseProfiles
        (FormulaShapeDirectionOrdering.shape (descriptors source)) =
      (retainedFigureNineClearancePositionedFormula source).clauses.map
        fun clause =>
          clauseProfile (literalProfiles clause.literals) := by
  rw [show
      FormulaShapeDirectionOrdering.shape (descriptors source) =
        shape source by rfl]
  rw [shape_eq_sourceShape source sourceWidth sourceClausesNonempty]
  rw [FormulaShapeRetainedFigureNineSource.clauseProfiles_shape]
  exact FormulaShapeOfFormula.profiles_erase _

/-- Projecting parent coordinates from the retained indexed finite blocks
gives exactly the parent coordinates of the concrete composed metadata list. -/
theorem indexedProfileCoordinateBlocks_map_parent_eq_metadata
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ((descriptors source).flatMap
      expectedIndexedProfileCoordinateBlocks).map
        IndexedProfileCoordinateBlock.parent =
      (formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source)).map
          ClauseMetadata.parentProfileCoordinate := by
  let clearance := retainedFigureNineClearancePositionedFormula source
  have clearanceWidth : clearance.erase.WidthAtMost 3 :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  have clearanceNonempty :
      ∀ clause ∈ clearance.clauses, clause.literals ≠ [] :=
    retainedFigureNineClearancePositionedFormula_clausesNonempty
      source sourceClausesNonempty
  calc
    _ = (FormulaShape.clauseProfiles
          (FormulaShapeDirectionOrdering.shape
            (descriptors source))).flatMap
              expectedParentProfileCoordinates :=
      source_flatMap_expectedIndexedProfileCoordinateBlocks_map_parent
        (descriptors source)
    _ = clearance.clauses.flatMap fun sourceClause =>
          expectedParentProfileCoordinates
            (clauseProfile
              (literalProfiles sourceClause.literals)) := by
      rw [clauseProfiles_shape_descriptors_eq_clearance
        source sourceWidth sourceClausesNonempty]
      simp only [clearance, List.flatMap_map]
    _ = _ :=
      (formulaClauseMetadata_map_parentProfileCoordinate
        clearance clearanceNonempty clearanceWidth).symm

end FormulaShapeRetainedFigureNineDirection
end PeriodicCNF
end LeanTrominoes
