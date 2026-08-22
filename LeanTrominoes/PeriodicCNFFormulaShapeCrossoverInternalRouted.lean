/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalRename
import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex

/-! # Routed clauses contain no crossover internals -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every routed source-clause metadata record contains no crossover-internal
atom. -/
theorem routedClauseMetadataClause_hasCrossoverInternal_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedClauseMetadata source) :
    embeddedClauseHasCrossoverInternal metadata.clause = false := by
  have clauseMember :
      metadata.clause ∈
        (drawingPlanarSATRoutedClauseMetadata source).map
          DrawingPlanarSATClauseMetadata.clause :=
    List.mem_map.mpr ⟨metadata, metadataMember, rfl⟩
  rw [drawingPlanarSATRoutedClauseMetadata_clauses] at clauseMember
  unfold scopedDrawingRoutedClauseFormula at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨clause, _clauseMember, clauseEq⟩
  rw [← clauseEq]
  exact embeddedClauseHasCrossoverInternal_rename_external_eq_false
    clause

/-- Every routed variable-gadget metadata record contains no
crossover-internal atom. -/
theorem routedVariableMetadataClause_hasCrossoverInternal_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataMember :
      metadata ∈ drawingPlanarSATRoutedVariableClauseMetadata source) :
    embeddedClauseHasCrossoverInternal metadata.clause = false := by
  have clauseMember :
      metadata.clause ∈
        (drawingPlanarSATRoutedVariableClauseMetadata source).map
          DrawingPlanarSATClauseMetadata.clause :=
    List.mem_map.mpr ⟨metadata, metadataMember, rfl⟩
  rw [drawingPlanarSATRoutedVariableClauseMetadata_clauses]
    at clauseMember
  unfold scopedDrawingRoutedVariableFormula at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨clause, _clauseMember, clauseEq⟩
  rw [← clauseEq]
  exact embeddedClauseHasCrossoverInternal_rename_external_eq_false
    clause

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
