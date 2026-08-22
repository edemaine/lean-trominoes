/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalCoreCarrierRename
import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex

/-! # Carrier and bend clauses contain no crossover internals -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every retained carrier metadata clause contains no crossover-internal
atom. -/
theorem retainedCarrierMetadataClause_hasCrossoverInternal_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataMember :
      metadata ∈ retainedDrawingPlanarSATCarrierClauseMetadata
        source.incidenceGraph) :
    embeddedClauseHasCrossoverInternal metadata.clause = false := by
  have clauseMember :
      metadata.clause ∈
        (retainedDrawingPlanarSATCarrierClauseMetadata
          source.incidenceGraph).map
            DrawingPlanarSATClauseMetadata.clause :=
    List.mem_map.mpr ⟨metadata, metadataMember, rfl⟩
  rw [retainedDrawingPlanarSATCarrierClauseMetadata_clauses]
    at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨clause, _clauseMember, clauseEq⟩
  rw [← clauseEq]
  exact
    embeddedClauseHasCrossoverInternal_doubleRename_coreCarrier_eq_false
      clause

/-- Every bend metadata clause contains no crossover-internal atom. -/
theorem bendMetadataClause_hasCrossoverInternal_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataMember :
      metadata ∈ drawingPlanarSATBendClauseMetadata
        source.incidenceGraph) :
    embeddedClauseHasCrossoverInternal metadata.clause = false := by
  have clauseMember :
      metadata.clause ∈
        (drawingPlanarSATBendClauseMetadata
          source.incidenceGraph).map
            DrawingPlanarSATClauseMetadata.clause :=
    List.mem_map.mpr ⟨metadata, metadataMember, rfl⟩
  rw [drawingPlanarSATBendClauseMetadata_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨clause, _clauseMember, clauseEq⟩
  rw [← clauseEq]
  exact
    embeddedClauseHasCrossoverInternal_doubleRename_coreCarrier_eq_false
      clause

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
