/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOneInThreeThreePositioned

/-!
# Indexing the positioned Figure 9 replacement

The positioned Figure 9 formula is a `flatMap` of variable-size local
clause blocks.  A global incidence route must recover the source clause and
the local generated-clause index from an output clause's flattened
presentation index.

This module stores that information in a parallel metadata list.  Projecting
the generated clause from every metadata entry recovers the existing
positioned formula exactly.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Source and local indexing information for one generated Figure 9
clause. -/
structure ClauseMetadata
    (Variable : Type*) where
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  clause :
    PositionedPeriodicClause
      (OneInThreeVariable Variable)
  localClauseIndex : Nat

/-- Index every generated clause in one source clause's Figure 9 block. -/
def clauseMetadataFor
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    List (ClauseMetadata Variable) :=
  (clauseGadget sourceClauseIndex sourceClause).zipIdx.map
    fun taggedClause =>
      ⟨sourceClause, sourceClauseIndex,
        taggedClause.1, taggedClause.2⟩

/-- Metadata parallel to the complete flattened positioned Figure 9
formula. -/
def formulaClauseMetadata
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    List (ClauseMetadata Variable) :=
  source.clauses.zipIdx.flatMap fun taggedSource =>
    clauseMetadataFor taggedSource.2 taggedSource.1

@[simp]
theorem clauseMetadataFor_clauses
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (clauseMetadataFor
      sourceClauseIndex sourceClause).map
        ClauseMetadata.clause =
      clauseGadget sourceClauseIndex sourceClause := by
  simp [clauseMetadataFor, List.map_map,
    Function.comp_def]

/-- A local metadata entry retains its source clause and genuine local
generated-clause index. -/
theorem clauseMetadataFor_valid
    {Variable : Type*}
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        clauseMetadataFor sourceClauseIndex sourceClause) :
    metadata.sourceClause = sourceClause ∧
      metadata.sourceClauseIndex = sourceClauseIndex ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (clauseGadget
          sourceClauseIndex sourceClause).zipIdx := by
  rw [clauseMetadataFor] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember,
      metadataEqual⟩
  subst metadata
  exact ⟨rfl, rfl, taggedClauseMember⟩

/-- Forgetting the indexing metadata recovers the existing positioned
Figure 9 formula. -/
@[simp]
theorem formulaClauseMetadata_clauses
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable) :
    (formulaClauseMetadata source).map
        ClauseMetadata.clause =
      (formula source).clauses := by
  simp [formulaClauseMetadata, formula,
    List.map_flatMap]

/-- Every global metadata entry retains a genuine source-clause membership
and a genuine local generated-clause membership. -/
theorem formulaClauseMetadata_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ formulaClauseMetadata source) :
    (metadata.sourceClause,
        metadata.sourceClauseIndex) ∈
      source.clauses.zipIdx ∧
    (metadata.clause, metadata.localClauseIndex) ∈
      (clauseGadget metadata.sourceClauseIndex
        metadata.sourceClause).zipIdx := by
  rw [formulaClauseMetadata,
    List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨taggedSource, taggedSourceMember,
      metadataMember⟩
  have valid :=
    clauseMetadataFor_valid
      taggedSource.2 taggedSource.1 metadataMember
  constructor
  · simpa [valid.1, valid.2.1] using
      taggedSourceMember
  · simpa [valid.1, valid.2.1] using
      valid.2.2

/-- Looking up a genuine flattened Figure 9 clause yields metadata carrying
that exact clause. -/
theorem formulaClauseMetadata_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause := by
  have clauseLookup :
      (formula source).clauses[clauseIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((formulaClauseMetadata source).map
          ClauseMetadata.clause)[clauseIndex]? =
        some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simpa only [Option.map_eq_some_iff] using
    projectedLookup

/-- A genuine flattened lookup also returns both membership invariants
needed to select the corresponding certified local drawing. -/
theorem formulaClauseMetadata_lookup_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (formula source).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause ∧
      (metadata.sourceClause,
          metadata.sourceClauseIndex) ∈
        source.clauses.zipIdx ∧
      (metadata.clause, metadata.localClauseIndex) ∈
        (clauseGadget metadata.sourceClauseIndex
          metadata.sourceClause).zipIdx := by
  rcases formulaClauseMetadata_lookup
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      formulaClauseMetadata_valid
        source metadataMember⟩

end PeriodicOneInThreePositioned
end LeanTrominoes
