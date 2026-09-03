/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFClauseProfilePolarityIndexedRouteOperationSemantics
import LeanTrominoes.PeriodicCNFClauseProfilePolarityNormalizationSemantics
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationExactRouteDirectionBlockList

/-! # Numeric route-operation schedule carried by polarity metadata -/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicCNF
open PeriodicCNF.ClauseProfilePolarityRouteOperation

/-- Numeric source-index/operation block encoded by one clause metadata
entry, independently of its positioned literal payload. -/
def metadataIndexedDescriptorBlock {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable) : List IndexedDescriptor :=
  match metadata.origin with
  | .normalized =>
      metadata.sourceClause.literals.zipIdx.map fun taggedLiteral =>
        normalizedIndexedDescriptor
          (taggedLiteral.1.value, taggedLiteral.2)
  | .complement sourceLiteralIndex _ =>
      [⟨sourceLiteralIndex, .complementFresh⟩,
        ⟨sourceLiteralIndex, .complementOriginal⟩]

/-- Numeric descriptor read directly at one output literal position. -/
def metadataIndexedDescriptorAt {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (literalIndex : Nat) : IndexedDescriptor where
  sourceLiteralIndex :=
    sourceLiteralIndexForMetadata metadata literalIndex
  operation := operationForMetadata metadata literalIndex

/-- Global source-incidence coordinates together with their selected route
operation. -/
structure SourceIndexedDescriptor where
  sourceClauseIndex : Nat
  sourceLiteralIndex : Nat
  operation : Operation
  deriving DecidableEq, Inhabited

/-- Attach one parent source-clause index to a numeric local descriptor. -/
def sourceIndexedDescriptorOf (sourceClauseIndex : Nat)
    (descriptor : IndexedDescriptor) : SourceIndexedDescriptor where
  sourceClauseIndex := sourceClauseIndex
  sourceLiteralIndex := descriptor.sourceLiteralIndex
  operation := descriptor.operation

/-- Project the exact source coordinates and operation from one compact
metadata route block. -/
def RouteDirectionBlock.sourceIndexedDescriptor :
    RouteDirectionBlock (Nat × Nat) → SourceIndexedDescriptor
  | .compatible sourceIndex =>
      ⟨sourceIndex.1, sourceIndex.2, .compatible⟩
  | .incompatible sourceIndex =>
      ⟨sourceIndex.1, sourceIndex.2, .incompatible⟩
  | .complementFresh sourceIndex =>
      ⟨sourceIndex.1, sourceIndex.2, .complementFresh⟩
  | .complementOriginal sourceIndex =>
      ⟨sourceIndex.1, sourceIndex.2, .complementOriginal⟩

/-- The compact block projection is precisely the metadata descriptor at
that output literal index. -/
@[simp] theorem exactRouteBlockForMetadata_sourceIndexedDescriptor
    {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (literalIndex : Nat) :
    (exactRouteBlockForMetadata metadata literalIndex).sourceIndexedDescriptor =
      sourceIndexedDescriptorOf metadata.sourceClauseIndex
        (metadataIndexedDescriptorAt metadata literalIndex) := by
  unfold exactRouteBlockForMetadata
    RouteDirectionBlock.sourceIndexedDescriptor
    metadataIndexedDescriptorAt sourceIndexedDescriptorOf
  generalize operationEq : operationForMetadata metadata literalIndex =
    operation
  cases operation <;> rfl

/-- On genuine metadata, the origin-based descriptor block is exactly the
consecutive output-literal scan used by the exact route-block list. -/
theorem metadataIndexedDescriptorBlock_eq_range_map
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (metadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          positions source) :
    metadataIndexedDescriptorBlock metadata =
      (List.range metadata.clause.literals.length).map
        (metadataIndexedDescriptorAt metadata) := by
  rcases metadata with
    ⟨sourceClause, sourceClauseIndex, clause, origin⟩
  cases origin with
  | normalized =>
      have clauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
          positions source metadataMember rfl
      dsimp only at clauseEq
      subst clause
      apply List.ext_getElem
      · simp [metadataIndexedDescriptorBlock,
          PeriodicOneInThreePolarityNormalizationPositioned.normalizedClause,
          PeriodicOneInThreePolarityNormalization.normalizeClause,
          PeriodicOneInThreePolarityNormalization.normalizeClauseFrom]
      · intro index leftLt rightLt
        have sourceIndexLt : index < sourceClause.literals.length := by
          simpa [metadataIndexedDescriptorBlock] using leftLt
        simp only [metadataIndexedDescriptorBlock,
          List.getElem_map, List.getElem_zipIdx, List.getElem_range]
        simp [metadataIndexedDescriptorAt, normalizedIndexedDescriptor,
          sourceLiteralIndexForMetadata, operationForMetadata,
          List.getElem?_eq_getElem sourceIndexLt,
          PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity_eq_semantic]
  | complement sourceLiteralIndex sourceLiteral =>
      have clauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
          positions source metadataMember rfl
      dsimp only at clauseEq
      subst clause
      change
        [⟨sourceLiteralIndex, .complementFresh⟩,
          ⟨sourceLiteralIndex, .complementOriginal⟩] =
        [metadataIndexedDescriptorAt _ 0,
          metadataIndexedDescriptorAt _ 1]
      rfl

/-- Projecting the complete exact block list gives the origin-based metadata
descriptor blocks in the same output presentation order. -/
theorem exactMetadataRouteBlocks_map_sourceIndexedDescriptor
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes) :
    (exactMetadataRouteBlocks source sourcePlacement sourceRoutes).map
        RouteDirectionBlock.sourceIndexedDescriptor =
      (clauseMetadata source sourcePlacement sourceRoutes).flatMap
        fun metadata =>
          (metadataIndexedDescriptorBlock metadata).map
            (sourceIndexedDescriptorOf metadata.sourceClauseIndex) := by
  unfold exactMetadataRouteBlocks
  rw [List.map_flatMap]
  refine (PeriodicCNF.zipIdx_flatMap_fst
    (fun metadata =>
      ((List.range metadata.clause.literals.length).map
        (exactRouteBlockForMetadata metadata)).map
          RouteDirectionBlock.sourceIndexedDescriptor)
    (clauseMetadata source sourcePlacement sourceRoutes) 0).trans ?_
  apply List.flatMap_congr
  intro metadata metadataMember
  have baseMetadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement sourceRoutes)
          (refinedSource source sourcePlacement) := by
    simpa only [clauseMetadata] using metadataMember
  rw [metadataIndexedDescriptorBlock_eq_range_map
    (rawPositions sourcePlacement sourceRoutes)
    (refinedSource source sourcePlacement)
    metadata baseMetadataMember]
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro literalIndex _literalIndexMember
  exact exactRouteBlockForMetadata_sourceIndexedDescriptor
    metadata literalIndex

/-- Filtered complement metadata emits exactly the generic complement
operation block for every incompatible literal in the indexed suffix. -/
theorem complementClauseMetadataFrom_flatMap_metadataIndexedDescriptorBlock
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom
        positions sourceClause sourceClauseIndex literalStart source).flatMap
        metadataIndexedDescriptorBlock =
      (source.zipIdx literalStart).flatMap fun taggedLiteral =>
        complementIndexedDescriptorBlock
          (taggedLiteral.1.value, taggedLiteral.2) := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value =
            PeriodicOneInThreePolarityNormalization.normalizedPolarity
              literalStart
      · simp [
          PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom,
          complementIndexedDescriptorBlock, compatible,
          PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity_eq_semantic,
          induction (literalStart + 1)]
      · simp [
          PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom,
          complementIndexedDescriptorBlock, metadataIndexedDescriptorBlock,
          compatible,
          PeriodicCNF.ClauseProfilePolarityNormalization.normalizedPolarity_eq_semantic,
          induction (literalStart + 1)]

/-- One source clause's metadata block carries the normalized main
operations followed by exactly its generic complement-operation suffix. -/
theorem clauseMetadataFor_flatMap_metadataIndexedDescriptorBlock
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor
        positions sourceClauseIndex sourceClause).flatMap
        metadataIndexedDescriptorBlock =
      indexedDescriptors
        (sourceClause.literals.map PeriodicLiteral.value) := by
  unfold PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor
    indexedDescriptors
  simp only [List.flatMap_cons]
  rw [complementClauseMetadataFrom_flatMap_metadataIndexedDescriptorBlock]
  unfold metadataIndexedDescriptorBlock
  rw [List.zipIdx_map, List.map_map, List.flatMap_map]
  rfl

/-- The complete polarity metadata list carries the generic numeric
operation schedule of the complete positioned source presentation. -/
theorem formulaClauseMetadata_flatMap_metadataIndexedDescriptorBlock
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions source).flatMap metadataIndexedDescriptorBlock =
      source.clauses.zipIdx.flatMap fun taggedClause =>
        indexedDescriptors
          (taggedClause.1.literals.map PeriodicLiteral.value) := by
  unfold
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedClause _taggedClauseMember
  exact clauseMetadataFor_flatMap_metadataIndexedDescriptorBlock
    positions taggedClause.2 taggedClause.1

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
