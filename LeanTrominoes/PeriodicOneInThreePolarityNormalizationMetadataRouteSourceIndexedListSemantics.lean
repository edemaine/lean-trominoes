/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteOperationSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRoutedOriginalOccurrenceProvenance

/-! # Globally source-indexed semantic polarity-operation lists -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicOneInThreePolarityNormalizationPositioned

/-- One source clause's metadata operations all retain that clause's global
presentation index. -/
theorem clauseMetadataFor_flatMap_sourceIndexedDescriptor
    {Variable : Type}
    (positions : Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (clauseMetadataFor positions sourceClauseIndex sourceClause).flatMap
        (fun metadata =>
          (metadataIndexedDescriptorBlock metadata).map
            (sourceIndexedDescriptorOf metadata.sourceClauseIndex)) =
      (indexedDescriptors
        (sourceClause.literals.map PeriodicLiteral.value)).map
          (sourceIndexedDescriptorOf sourceClauseIndex) := by
  calc
    _ = (clauseMetadataFor positions sourceClauseIndex sourceClause).flatMap
          (fun metadata =>
            (metadataIndexedDescriptorBlock metadata).map
              (sourceIndexedDescriptorOf sourceClauseIndex)) := by
      apply List.flatMap_congr
      intro metadata metadataMember
      rw [clauseMetadataFor_sourceClauseIndex
        positions sourceClauseIndex sourceClause metadataMember]
    _ = ((clauseMetadataFor positions sourceClauseIndex sourceClause).flatMap
          metadataIndexedDescriptorBlock).map
            (sourceIndexedDescriptorOf sourceClauseIndex) := by
      rw [List.map_flatMap]
    _ = _ := by
      rw [clauseMetadataFor_flatMap_metadataIndexedDescriptorBlock]

/-- Across the complete formula, semantic metadata retains the exact global
source-clause index together with every local literal index and operation. -/
theorem formulaClauseMetadata_flatMap_sourceIndexedDescriptor
    {Variable : Type}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    (formulaClauseMetadata positions source).flatMap
        (fun metadata =>
          (metadataIndexedDescriptorBlock metadata).map
            (sourceIndexedDescriptorOf metadata.sourceClauseIndex)) =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        (indexedDescriptors
          (taggedClause.1.literals.map PeriodicLiteral.value)).map
            (sourceIndexedDescriptorOf taggedClause.2) := by
  unfold formulaClauseMetadata
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  exact clauseMetadataFor_flatMap_sourceIndexedDescriptor
    positions taggedClause.2 taggedClause.1

/-- Anchor normalization and coordinate refinement preserve clause indices,
literal values, and hence the globally source-indexed operation schedule. -/
theorem refinedSource_zipIdx_flatMap_sourceIndexedDescriptor
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    (refinedSource source sourcePlacement).clauses.zipIdx.flatMap
        (fun taggedClause =>
          (indexedDescriptors
            (taggedClause.1.literals.map PeriodicLiteral.value)).map
              (sourceIndexedDescriptorOf taggedClause.2)) =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        (indexedDescriptors
          (taggedClause.1.literals.map PeriodicLiteral.value)).map
            (sourceIndexedDescriptorOf taggedClause.2) := by
  simp only [refinedSource, PositionedPeriodicCNF.scale,
    PositionedPeriodicCNF.anchorNormalize,
    PositionedPeriodicClause.scale, PeriodicClause.anchorNormalize,
    List.zipIdx_map, List.flatMap_map, List.map_map,
    Function.comp_apply, Prod.map, id_eq]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  apply congrArg (List.map
    (sourceIndexedDescriptorOf taggedClause.2))
  apply congrArg indexedDescriptors
  apply List.map_congr_left
  intro literal _literalMember
  rfl

/-- Consequently the complete exact route-block list projects to the same
globally source-indexed clause-major operation schedule. -/
theorem exactMetadataRouteBlocks_map_sourceIndexedDescriptor_eq_values
    {Variable : Type}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
        RouteDirectionBlock.sourceIndexedDescriptor =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        (indexedDescriptors
          (taggedClause.1.literals.map PeriodicLiteral.value)).map
            (sourceIndexedDescriptorOf taggedClause.2) := by
  exact
    ((exactMetadataRouteBlocks_map_sourceIndexedDescriptor
        source sourcePlacement sourceRoutes).trans
        (formulaClauseMetadata_flatMap_sourceIndexedDescriptor
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement))).trans
      (refinedSource_zipIdx_flatMap_sourceIndexedDescriptor
        source sourcePlacement)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
