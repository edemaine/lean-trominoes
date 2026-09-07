/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockList

/-! # Exact polarity direction lists from geometry of genuine incidences -/

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

open Gadget PeriodicOrthocrossing

/-- Geometry of the genuine source incidences discharges the metadata-level
geometry premise for the complete exact polarity direction-word list. -/
theorem presentedIncidenceDirectionWords_formula_eq_exactMetadataRouteBlocks_of_members
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceGeometry :
      ∀ {sourceClause : PositionedPeriodicClause Variable} {clauseIndex : Nat},
        (sourceClause, clauseIndex) ∈ source.clauses.zipIdx →
        ∀ {sourceLiteral : PeriodicLiteral Variable} {literalIndex : Nat},
          (sourceLiteral, literalIndex) ∈ sourceClause.literals.zipIdx →
          2 ≤ (sourceRoutes clauseIndex literalIndex).length ∧
            OrthogonalPolyline (sourceRoutes clauseIndex literalIndex)) :
    presentedIncidenceDirectionWords
        (formula source sourcePlacement sourceRoutes)
        (incidenceRoutes source sourcePlacement sourceRoutes) =
      (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
        (fun block => block.directions (fun sourceIndex =>
          unitSubdivisionDirections (sourceRoutes sourceIndex.1 sourceIndex.2))) := by
  apply presentedIncidenceDirectionWords_formula_eq_exactMetadataRouteBlocks
  intro metadata metadataMember literalIndex literalLt
  have baseMember : metadata ∈
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement sourceRoutes)
        (refinedSource source sourcePlacement) := metadataMember
  have refinedClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
      (rawPositions sourcePlacement sourceRoutes)
      (refinedSource source sourcePlacement) baseMember
  cases originEq : metadata.origin with
  | normalized =>
    have clauseEq :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
        (rawPositions sourcePlacement sourceRoutes)
        (refinedSource source sourcePlacement) baseMember originEq
    have sourceLt : literalIndex < metadata.sourceClause.literals.length := by
      rw [clauseEq] at literalLt
      simpa [PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
        PeriodicOneInThreePolarityNormalization.normalizeClause,
        PeriodicOneInThreePolarityNormalization.normalizeClauseFrom] using literalLt
    have refinedLiteralMember :
        (metadata.sourceClause.literals[literalIndex], literalIndex) ∈
          metadata.sourceClause.literals.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem sourceLt)
    obtain ⟨_, _, clauseMember, literalMember⟩ :=
      exists_source_members_of_refinedSource_members
        source sourcePlacement refinedClauseMember refinedLiteralMember
    simpa only [sourceLiteralIndexForMetadata, originEq] using
      sourceGeometry clauseMember literalMember
  | complement sourceLiteralIndex sourceLiteral =>
    have valid :=
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
        (rawPositions sourcePlacement sourceRoutes)
        (refinedSource source sourcePlacement) baseMember originEq
    obtain ⟨_, _, clauseMember, literalMember⟩ :=
      exists_source_members_of_refinedSource_members
        source sourcePlacement valid.1 valid.2.1
    simpa only [sourceLiteralIndexForMetadata, originEq] using
      sourceGeometry clauseMember literalMember

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
