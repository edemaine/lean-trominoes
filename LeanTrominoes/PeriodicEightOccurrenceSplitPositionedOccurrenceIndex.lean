/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitPositioned

/-!
# Indexing copied source clauses in positioned occurrence splitting

The prefix of the positioned fixed-eight formula is a pointwise copy of the
source clause list.  Its clauses and literals retain their presentation
indices, but each source literal is redirected to the compass copy selected
by the occurrence-port assignment.

This module records that correspondence explicitly.  Later geometric route
splicing can therefore recover the original positioned incidence, reuse its
route, and identify the exact fixed-copy endpoint without unfolding nested
`zipIdx.map` definitions.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

/-- Source information retained at one copied-clause index. -/
structure OccurrenceClauseMetadata
    (Variable : Type*) where
  sourceClause : PositionedPeriodicClause Variable
  clauseIndex : Nat
  clause :
    PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable)

/-- Metadata parallel to the copied source-clause prefix. -/
def occurrenceClauseMetadata
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts) :
    List (OccurrenceClauseMetadata Variable) :=
  source.clauses.zipIdx.map fun taggedClause =>
    ⟨taggedClause.1, taggedClause.2,
      occurrenceClause occurrencePorts
        taggedClause.2 taggedClause.1⟩

@[simp]
theorem occurrenceClauseMetadata_clauses
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts) :
    (occurrenceClauseMetadata
        source occurrencePorts).map
        OccurrenceClauseMetadata.clause =
      occurrenceClauses source occurrencePorts := by
  simp [occurrenceClauseMetadata, occurrenceClauses,
    List.map_map, Function.comp_def]

/-- Every metadata entry retains the genuine source clause at the same
presentation index and is exactly its positioned copied image. -/
theorem occurrenceClauseMetadata_valid
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {metadata : OccurrenceClauseMetadata Variable}
    (metadataMember :
      metadata ∈
        occurrenceClauseMetadata source occurrencePorts) :
    (metadata.sourceClause, metadata.clauseIndex) ∈
        source.clauses.zipIdx ∧
      metadata.clause =
        occurrenceClause occurrencePorts
          metadata.clauseIndex metadata.sourceClause := by
  rw [occurrenceClauseMetadata] at metadataMember
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember,
      metadataEqual⟩
  subst metadata
  exact ⟨taggedClauseMember, rfl⟩

/-- A genuine copied clause index retrieves metadata carrying that exact
clause. -/
theorem occurrenceClauseMetadata_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (occurrenceClauses
          source occurrencePorts).zipIdx) :
    ∃ metadata,
      (occurrenceClauseMetadata
          source occurrencePorts)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause ∧
      (metadata.sourceClause, metadata.clauseIndex) ∈
        source.clauses.zipIdx ∧
      metadata.clauseIndex = clauseIndex ∧
      metadata.clause =
        occurrenceClause occurrencePorts
          metadata.clauseIndex metadata.sourceClause := by
  have clauseLookup :
      (occurrenceClauses
          source occurrencePorts)[clauseIndex]? =
        some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((occurrenceClauseMetadata
          source occurrencePorts).map
          OccurrenceClauseMetadata.clause)[clauseIndex]? =
        some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simp only [Option.map_eq_some_iff] at projectedLookup
  rcases projectedLookup with
    ⟨metadata, metadataLookup, clauseEqual⟩
  have metadataIndexLt :
      clauseIndex <
        (occurrenceClauseMetadata
          source occurrencePorts).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (occurrenceClauseMetadata
          source occurrencePorts)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        occurrenceClauseMetadata
          source occurrencePorts := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have valid :=
    occurrenceClauseMetadata_valid
      source occurrencePorts metadataMember
  have metadataIndex :
      metadata.clauseIndex = clauseIndex := by
    have sourceIndexLt :
        clauseIndex < source.clauses.length := by
      simpa [occurrenceClauseMetadata] using
        metadataIndexLt
    have metadataAtClosed :
        (occurrenceClauseMetadata
          source occurrencePorts)[clauseIndex] =
          ⟨source.clauses[clauseIndex],
            clauseIndex,
            occurrenceClause occurrencePorts
              clauseIndex
              source.clauses[clauseIndex]⟩ := by
      simp [occurrenceClauseMetadata,
        List.getElem_zipIdx]
    have metadataEqual :
        metadata =
          ⟨source.clauses[clauseIndex],
            clauseIndex,
            occurrenceClause occurrencePorts
              clauseIndex
              source.clauses[clauseIndex]⟩ :=
      metadataAt.symm.trans metadataAtClosed
    exact congrArg
      OccurrenceClauseMetadata.clauseIndex
      metadataEqual
  exact
    ⟨metadata, metadataLookup, clauseEqual,
      valid.1, metadataIndex, valid.2⟩

/-- A copied literal at a genuine clause/literal index comes from the source
literal at the same indices and names exactly the selected compass copy. -/
theorem occurrenceLiteral_of_members
    {Variable : Type*}
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {sourceClause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    (clauseEqual :
      clause =
        occurrenceClause occurrencePorts
          clauseIndex sourceClause)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    ∃ sourceLiteral,
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx ∧
      literal =
        PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts clauseIndex literalIndex
          sourceLiteral := by
  subst clause
  have copiedLiteralIndexLt :
      literalIndex <
        (PeriodicEightOccurrenceSplit.occurrenceClause
          occurrencePorts clauseIndex
          sourceClause.literals).length :=
    (List.mem_zipIdx' literalMember).1
  have sourceLiteralIndexLt :
      literalIndex < sourceClause.literals.length := by
    simpa [PeriodicEightOccurrenceSplit.occurrenceClause_length] using
      copiedLiteralIndexLt
  let sourceLiteral :=
    sourceClause.literals[literalIndex]
  have sourceLiteralMember :
      (sourceLiteral, literalIndex) ∈
        sourceClause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨sourceLiteralIndexLt, rfl⟩
  have literalEqual :
      literal =
        PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts clauseIndex
          literalIndex sourceLiteral := by
    rw [(List.mem_zipIdx' literalMember).2]
    change
      (PeriodicEightOccurrenceSplit.occurrenceClause
        occurrencePorts clauseIndex
        sourceClause.literals)[literalIndex] =
      PeriodicEightOccurrenceSplit.occurrenceLiteral
        occurrencePorts clauseIndex literalIndex
        sourceLiteral
    simp [PeriodicEightOccurrenceSplit.occurrenceClause,
      sourceLiteral, List.getElem_zipIdx]
  exact
    ⟨sourceLiteral, sourceLiteralMember,
      literalEqual⟩

/-- Combined clause and literal lookup for the copied source prefix. -/
theorem occurrenceMetadata_of_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (occurrenceClauses
          source occurrencePorts).zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        clause.literals.zipIdx) :
    ∃ metadata : OccurrenceClauseMetadata Variable,
      ∃ sourceLiteral : PeriodicLiteral Variable,
      metadata.clause = clause ∧
      metadata.clauseIndex = clauseIndex ∧
      (metadata.sourceClause, clauseIndex) ∈
        source.clauses.zipIdx ∧
      (sourceLiteral, literalIndex) ∈
        metadata.sourceClause.literals.zipIdx ∧
      literal =
        PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts clauseIndex literalIndex
          sourceLiteral := by
  rcases occurrenceClauseMetadata_lookup
      source occurrencePorts clauseMember with
    ⟨metadata, _metadataLookup, metadataClauseEqual,
      sourceClauseMember, metadataIndex,
      metadataClauseDefinition⟩
  have sourceClauseMemberAt :
      (metadata.sourceClause, clauseIndex) ∈
        source.clauses.zipIdx := by
    simpa [metadataIndex] using sourceClauseMember
  have copiedClauseEqual :
      clause =
        occurrenceClause occurrencePorts
          clauseIndex metadata.sourceClause := by
    calc
      clause = metadata.clause :=
        metadataClauseEqual.symm
      _ =
          occurrenceClause occurrencePorts
            metadata.clauseIndex metadata.sourceClause :=
        metadataClauseDefinition
      _ =
          occurrenceClause occurrencePorts
            clauseIndex metadata.sourceClause := by
        rw [metadataIndex]
  rcases occurrenceLiteral_of_members
      occurrencePorts copiedClauseEqual literalMember with
    ⟨sourceLiteral, sourceLiteralMember,
      literalEqual⟩
  exact
    ⟨metadata, sourceLiteral, metadataClauseEqual,
      metadataIndex, sourceClauseMemberAt,
      sourceLiteralMember, literalEqual⟩

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
