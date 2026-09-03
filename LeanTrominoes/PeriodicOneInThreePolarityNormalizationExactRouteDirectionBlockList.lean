/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMappedZipIdx
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlock

/-! # Presentation list of exact routed polarity blocks -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open Gadget PeriodicOrthocrossing

/-- Incidence direction words of a positioned formula in clause-major,
literal-minor presentation order. -/
def presentedIncidenceDirectionWords {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (List AxisDirection) :=
  source.clauses.zipIdx.flatMap fun taggedClause =>
    taggedClause.1.literals.zipIdx.map fun taggedLiteral =>
      unitSubdivisionDirections
        (routes taggedClause.2 taggedLiteral.2)

/-- Canonical metadata-selected blocks in the same flattened output
incidence order as routed polarity normalization. -/
def exactMetadataRouteBlocks {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (RouteDirectionBlock (Nat × Nat)) :=
  (clauseMetadata source sourcePlacement sourceRoutes).zipIdx.flatMap
    fun taggedMetadata =>
      (List.range taggedMetadata.1.clause.literals.length).map
        (exactRouteBlockForMetadata taggedMetadata.1)

/-- Flattening the exact metadata theorem yields the whole routed output
direction column in clause-major, literal-minor order. -/
theorem presentedIncidenceDirectionWords_formula_eq_exactMetadataRouteBlocks
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceGeometry :
      ∀ metadata,
        metadata ∈ clauseMetadata source sourcePlacement sourceRoutes →
        ∀ literalIndex,
          literalIndex < metadata.clause.literals.length →
          2 ≤ (sourceRoutes metadata.sourceClauseIndex
              (sourceLiteralIndexForMetadata metadata literalIndex)).length ∧
            OrthogonalPolyline
              (sourceRoutes metadata.sourceClauseIndex
                (sourceLiteralIndexForMetadata metadata literalIndex))) :
    presentedIncidenceDirectionWords
        (formula source sourcePlacement sourceRoutes)
        (incidenceRoutes source sourcePlacement sourceRoutes) =
      (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
        fun block => block.directions fun sourceIndex =>
          unitSubdivisionDirections
            (sourceRoutes sourceIndex.1 sourceIndex.2) := by
  unfold presentedIncidenceDirectionWords exactMetadataRouteBlocks
  rw [show
      (formula source sourcePlacement sourceRoutes).clauses =
        (clauseMetadata source sourcePlacement sourceRoutes).map
          fun metadata =>
            { position := metadata.clause.position
              literals := metadata.clause.literals.variableGauge freshGauge }
      by
        unfold formula PositionedPeriodicCNF.variableGauge
        rw [show
          (rawFormula source sourcePlacement sourceRoutes).clauses =
            (clauseMetadata source sourcePlacement sourceRoutes).map
              PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata.clause
          from (clauseMetadata_clauses
            source sourcePlacement sourceRoutes).symm]
        rw [List.map_map]
        rfl]
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  simp only [List.map_map]
  apply List.flatMap_congr
  intro taggedMetadata taggedMetadataMember
  have metadataMember :
      taggedMetadata.1 ∈
        clauseMetadata source sourcePlacement sourceRoutes :=
    List.fst_mem_of_mem_zipIdx taggedMetadataMember
  have metadataLookup :
      (clauseMetadata source sourcePlacement sourceRoutes)[
          taggedMetadata.2]? = some taggedMetadata.1 :=
    (List.mem_zipIdx_iff_getElem?).mp taggedMetadataMember
  change
    List.map
        (fun taggedLiteral =>
          unitSubdivisionDirections
            (incidenceRoutes source sourcePlacement sourceRoutes
              taggedMetadata.2 taggedLiteral.2))
        ((taggedMetadata.1.clause.literals.variableGauge freshGauge).zipIdx) =
      List.map
        (fun literalIndex =>
          (exactRouteBlockForMetadata
              taggedMetadata.1 literalIndex).directions
            fun sourceIndex =>
              unitSubdivisionDirections
                (sourceRoutes sourceIndex.1 sourceIndex.2))
        (List.range taggedMetadata.1.clause.literals.length)
  apply List.ext_getElem
  · simp
  · intro literalIndex leftLt rightLt
    simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range]
    simpa only [Nat.zero_add] using
      incidenceRoutes_directionWord_eq_exactRouteBlockForMetadata
        source sourcePlacement sourceRoutes taggedMetadata.1
        taggedMetadata.2 literalIndex metadataLookup metadataMember
        (by simpa using rightLt)
        (sourceGeometry taggedMetadata.1 metadataMember literalIndex
          (by simpa using rightLt))

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
