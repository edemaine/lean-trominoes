/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteDirectionBlock

/-! # Canonical compact blocks for routed polarity normalization

The earlier route theorem classifies every output incidence existentially.
Here the polarity metadata selects the exact source incidence and one of the
four compact operations.  This form can be compared pointwise with an
independently compiled route-header stream.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open Gadget PeriodicOrthocrossing

/-- Source literal index supplying the route of one metadata-classified
output incidence. -/
def sourceLiteralIndexForMetadata {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (literalIndex : Nat) : Nat :=
  match metadata.origin with
  | .normalized => literalIndex
  | .complement sourceLiteralIndex _ => sourceLiteralIndex

/-- The canonical compact route operation selected by polarity metadata.
The fallbacks are irrelevant for genuine output literal indices. -/
def exactRouteBlockForMetadata {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (literalIndex : Nat) : RouteDirectionBlock (Nat × Nat) :=
  let sourceIndex :=
    (metadata.sourceClauseIndex,
      sourceLiteralIndexForMetadata metadata literalIndex)
  match metadata.origin with
  | .normalized =>
      match metadata.sourceClause.literals[literalIndex]? with
      | none => .compatible sourceIndex
      | some sourceLiteral =>
          if sourceLiteral.value =
              PeriodicOneInThreePolarityNormalization.normalizedPolarity
                literalIndex then
            .compatible sourceIndex
          else
            .incompatible sourceIndex
  | .complement _ _ =>
      if literalIndex = 0 then
        .complementFresh sourceIndex
      else
        .complementOriginal sourceIndex

/-- At a genuine metadata entry and literal index, the final routed
polarity-normalization word is the canonical metadata-selected compact
block, not merely some member of the four-operation vocabulary. -/
theorem incidenceRoutes_directionWord_eq_exactRouteBlockForMetadata
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (clauseIndex literalIndex : Nat)
    (metadataLookup :
      (clauseMetadata source sourcePlacement sourceRoutes)[clauseIndex]? =
        some metadata)
    (metadataMember :
      metadata ∈ clauseMetadata source sourcePlacement sourceRoutes)
    (literalIndexLt : literalIndex < metadata.clause.literals.length)
    (sourceGeometry :
      2 ≤ (sourceRoutes metadata.sourceClauseIndex
          (sourceLiteralIndexForMetadata metadata literalIndex)).length ∧
        OrthogonalPolyline
          (sourceRoutes metadata.sourceClauseIndex
            (sourceLiteralIndexForMetadata metadata literalIndex))) :
    unitSubdivisionDirections
        (incidenceRoutes source sourcePlacement sourceRoutes
          clauseIndex literalIndex) =
      (exactRouteBlockForMetadata metadata literalIndex).directions
        (fun sourceIndex =>
          unitSubdivisionDirections
            (sourceRoutes sourceIndex.1 sourceIndex.2)) := by
  have rawClauseLookup :
      (rawFormula source sourcePlacement sourceRoutes).clauses[
          clauseIndex]? = some metadata.clause := by
    rw [← clauseMetadata_clauses]
    rw [List.getElem?_map, metadataLookup]
    rfl
  have rawClauseMember :
      (metadata.clause, clauseIndex) ∈
        (rawFormula source sourcePlacement sourceRoutes).clauses.zipIdx :=
    (List.mem_zipIdx_iff_getElem?).mpr rawClauseLookup
  have outputDirections :=
    incidenceRoutes_directionWord_of_raw_clause_mem
      source sourcePlacement sourceRoutes rawClauseMember
      (literalIndex := literalIndex)
  rw [rawIncidenceRoutes_of_metadata_lookup
    source sourcePlacement sourceRoutes metadata
    clauseIndex literalIndex metadataLookup] at outputDirections
  cases originEq : metadata.origin with
  | normalized =>
      have normalizedClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement)
          (by simpa only [clauseMetadata] using metadataMember)
          originEq
      have sourceLiteralIndexLt :
          literalIndex < metadata.sourceClause.literals.length := by
        rw [normalizedClauseEq] at literalIndexLt
        simpa [
          PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
          PeriodicOneInThreePolarityNormalization.normalizeClause,
          PeriodicOneInThreePolarityNormalization.normalizeClauseFrom]
          using literalIndexLt
      have sourceLiteralLookup :
          metadata.sourceClause.literals[literalIndex]? =
            some metadata.sourceClause.literals[literalIndex] :=
        List.getElem?_eq_getElem sourceLiteralIndexLt
      have geometry :
          2 ≤ (sourceRoutes metadata.sourceClauseIndex literalIndex).length ∧
            OrthogonalPolyline
              (sourceRoutes metadata.sourceClauseIndex literalIndex) := by
        simpa [sourceLiteralIndexForMetadata, originEq] using sourceGeometry
      by_cases compatible :
          metadata.sourceClause.literals[literalIndex].value =
            PeriodicOneInThreePolarityNormalization.normalizedPolarity
              literalIndex
      · have rawDirections :=
          rawRouteForMetadata_normalized_compatible_directionWord
            sourcePlacement sourceRoutes metadata
            metadata.sourceClause.literals[literalIndex]
            literalIndex originEq sourceLiteralLookup compatible geometry.2
        exact outputDirections.trans (by
          simpa [exactRouteBlockForMetadata,
            sourceLiteralIndexForMetadata, originEq,
            sourceLiteralLookup, compatible,
            RouteDirectionBlock.directions] using rawDirections)
      · have rawDirections :=
          rawRouteForMetadata_normalized_incompatible_directionWord
            sourcePlacement sourceRoutes metadata
            metadata.sourceClause.literals[literalIndex]
            literalIndex originEq sourceLiteralLookup compatible geometry.2
        exact outputDirections.trans (by
          simpa [exactRouteBlockForMetadata,
            sourceLiteralIndexForMetadata, originEq,
            sourceLiteralLookup, compatible,
            RouteDirectionBlock.directions] using rawDirections)
  | complement sourceLiteralIndex sourceLiteral =>
      have baseMetadataMember :
          metadata ∈
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
              (rawPositions sourcePlacement sourceRoutes)
              (refinedSource source sourcePlacement) := by
        simpa only [clauseMetadata] using metadataMember
      have complementClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement)
          baseMetadataMember originEq
      have outputLiteralIndexLt : literalIndex < 2 := by
        rw [complementClauseEq] at literalIndexLt
        simpa [
          PeriodicOneInThreePolarityNormalizationPositioned.positionedComplementClause,
          PeriodicOneInThreePolarityNormalization.complementClause]
          using literalIndexLt
      have indexCases : literalIndex = 0 ∨ literalIndex = 1 := by omega
      have geometry :
          2 ≤ (sourceRoutes metadata.sourceClauseIndex
              sourceLiteralIndex).length ∧
            OrthogonalPolyline
              (sourceRoutes metadata.sourceClauseIndex
                sourceLiteralIndex) := by
        simpa [sourceLiteralIndexForMetadata, originEq] using sourceGeometry
      rcases indexCases with indexEq | indexEq
      · subst literalIndex
        have rawDirections :=
          rawRouteForMetadata_complement_fresh_directionWord
            sourcePlacement sourceRoutes metadata sourceLiteral
            sourceLiteralIndex originEq geometry.1 geometry.2
        exact outputDirections.trans (by
          simpa [exactRouteBlockForMetadata,
            sourceLiteralIndexForMetadata, originEq,
            RouteDirectionBlock.directions] using rawDirections)
      · subst literalIndex
        have rawDirections :=
          rawRouteForMetadata_complement_original_directionWord
            sourcePlacement sourceRoutes metadata sourceLiteral
            sourceLiteralIndex originEq geometry.2
        exact outputDirections.trans (by
          simpa [exactRouteBlockForMetadata,
            sourceLiteralIndexForMetadata, originEq,
            RouteDirectionBlock.directions] using rawDirections)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
