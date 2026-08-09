import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPositioned

/-!
# Indexing positioned polarity normalization

Positioned polarity normalization is a variable-size `flatMap`: every source
clause produces one normalized main clause and one binary complement clause
for each incompatible literal occurrence.  This file gives that flattened
list a parallel, lossless origin index.  In particular, every binary clause
retains the exact source literal and presentation index whose incidence route
will be subdivided.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationPositioned

open PeriodicOneInThreePolarityNormalization

/-- The geometric origin of one generated positioned clause. -/
inductive ClauseOrigin (Variable : Type*) where
  /-- The main clause keeps all source literal presentation indices. -/
  | normalized
  /-- A binary clause belongs to one incompatible source occurrence. -/
  | complement
      (sourceLiteralIndex : Nat)
      (sourceLiteral : PeriodicLiteral Variable)

/-- Source and origin information for one generated positioned clause. -/
structure ClauseMetadata (Variable : Type*) where
  sourceClause : PositionedPeriodicClause Variable
  sourceClauseIndex : Nat
  clause :
    PositionedPeriodicClause (PolarityNormalizedVariable Variable)
  origin : ClauseOrigin Variable

/-- Metadata for the filtered binary clauses generated from a literal
suffix. -/
def complementClauseMetadataFrom {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat) :
    PeriodicClause Variable → List (ClauseMetadata Variable)
  | [] => []
  | literal :: rest =>
      if literal.value = normalizedPolarity literalStart then
        complementClauseMetadataFrom positions sourceClause
          sourceClauseIndex (literalStart + 1) rest
      else
        { sourceClause := sourceClause
          sourceClauseIndex := sourceClauseIndex
          clause := positionedComplementClause positions sourceClauseIndex
            literalStart literal
          origin := .complement literalStart literal } ::
        complementClauseMetadataFrom positions sourceClause
          sourceClauseIndex (literalStart + 1) rest

/-- Projecting the generated clause from complement metadata recovers the
positioned complement-clause list exactly. -/
@[simp]
theorem complementClauseMetadataFrom_clauses {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (complementClauseMetadataFrom positions sourceClause
        sourceClauseIndex literalStart source).map ClauseMetadata.clause =
      positionedComplementClausesFrom positions sourceClauseIndex
        literalStart source := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [complementClauseMetadataFrom,
          positionedComplementClausesFrom_cons, compatible,
          induction (literalStart + 1)]
      · simp [complementClauseMetadataFrom,
          positionedComplementClausesFrom_cons, compatible,
          induction (literalStart + 1)]

/-- Metadata parallel to one source clause's complete replacement block. -/
def clauseMetadataFor {Variable : Type*}
    (positions : Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    List (ClauseMetadata Variable) :=
  { sourceClause := sourceClause
    sourceClauseIndex := sourceClauseIndex
    clause := normalizedClause sourceClauseIndex sourceClause
    origin := .normalized } ::
  complementClauseMetadataFrom positions sourceClause sourceClauseIndex 0
    sourceClause.literals

/-- Forgetting local origin metadata recovers one positioned replacement
block. -/
@[simp]
theorem clauseMetadataFor_clauses {Variable : Type*}
    (positions : Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    (clauseMetadataFor positions sourceClauseIndex sourceClause).map
        ClauseMetadata.clause =
      clauseBlock positions sourceClauseIndex sourceClause := by
  simp [clauseMetadataFor, clauseBlock]

/-- Metadata parallel to the complete flattened positioned normalization. -/
def formulaClauseMetadata {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    List (ClauseMetadata Variable) :=
  source.clauses.zipIdx.flatMap fun taggedSource =>
    clauseMetadataFor positions taggedSource.2 taggedSource.1

/-- Projecting all generated clauses recovers the positioned normalized
formula exactly. -/
@[simp]
theorem formulaClauseMetadata_clauses {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    (formulaClauseMetadata positions source).map ClauseMetadata.clause =
      (formula positions source).clauses := by
  simp [formulaClauseMetadata, formula, List.map_flatMap]

/-- Complement metadata never loses the source-clause fields threaded
through its filtered recursion. -/
theorem complementClauseMetadataFrom_source_eq {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ complementClauseMetadataFrom positions sourceClause
        sourceClauseIndex literalStart source) :
    metadata.sourceClause = sourceClause ∧
      metadata.sourceClauseIndex = sourceClauseIndex := by
  induction source generalizing literalStart metadata with
  | nil =>
      simp [complementClauseMetadataFrom] at metadataMember
  | cons literal rest induction =>
      simp only [complementClauseMetadataFrom] at metadataMember
      split at metadataMember
      · exact induction (literalStart + 1) metadataMember
      · simp only [List.mem_cons] at metadataMember
        rcases metadataMember with metadataEq | metadataMember
        · subst metadata
          exact ⟨rfl, rfl⟩
        · exact induction (literalStart + 1) metadataMember

/-- Filtered complement metadata can never masquerade as the normalized
main-clause origin. -/
theorem complementClauseMetadataFrom_origin_ne_normalized
    {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember :
      metadata ∈ complementClauseMetadataFrom positions sourceClause
        sourceClauseIndex literalStart source) :
    metadata.origin ≠ .normalized := by
  induction source generalizing literalStart metadata with
  | nil =>
      simp [complementClauseMetadataFrom] at metadataMember
  | cons literal rest induction =>
      simp only [complementClauseMetadataFrom] at metadataMember
      split at metadataMember
      · exact induction (literalStart + 1) metadataMember
      · simp only [List.mem_cons] at metadataMember
        rcases metadataMember with metadataEq | metadataMember
        · subst metadata
          simp
        · exact induction (literalStart + 1) metadataMember

/-- A complement origin in the filtered metadata is exactly a genuine
incompatible occurrence of the indexed literal suffix. -/
theorem complementClauseMetadataFrom_complement_valid {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    {sourceLiteralIndex : Nat}
    {sourceLiteral : PeriodicLiteral Variable}
    (metadataMember :
      metadata ∈ complementClauseMetadataFrom positions sourceClause
        sourceClauseIndex literalStart source)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    (sourceLiteral, sourceLiteralIndex) ∈ source.zipIdx literalStart ∧
      sourceLiteral.value ≠ normalizedPolarity sourceLiteralIndex := by
  induction source generalizing literalStart metadata with
  | nil =>
      simp [complementClauseMetadataFrom] at metadataMember
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · rw [complementClauseMetadataFrom, if_pos compatible]
          at metadataMember
        have valid := induction (literalStart + 1) metadataMember originEq
        exact ⟨by
          simpa using
            (Or.inr valid.1 :
              (sourceLiteral = literal ∧
                  sourceLiteralIndex = literalStart) ∨
                (sourceLiteral, sourceLiteralIndex) ∈
                  rest.zipIdx (literalStart + 1)), valid.2⟩
      · rw [complementClauseMetadataFrom, if_neg compatible]
          at metadataMember
        simp only [List.mem_cons] at metadataMember
        rcases metadataMember with metadataEq | metadataMember
        · subst metadata
          cases originEq
          exact ⟨by simp, compatible⟩
        · have valid := induction (literalStart + 1) metadataMember originEq
          exact ⟨by
            simpa using
              (Or.inr valid.1 :
                (sourceLiteral = literal ∧
                    sourceLiteralIndex = literalStart) ∨
                  (sourceLiteral, sourceLiteralIndex) ∈
                    rest.zipIdx (literalStart + 1)), valid.2⟩

/-- A classified complement origin carries exactly its positioned binary
clause, not merely the source-occurrence tag. -/
theorem complementClauseMetadataFrom_complement_clause_eq
    {Variable : Type*}
    (positions : Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable)
    {metadata : ClauseMetadata Variable}
    {sourceLiteralIndex : Nat}
    {sourceLiteral : PeriodicLiteral Variable}
    (metadataMember :
      metadata ∈ complementClauseMetadataFrom positions sourceClause
        sourceClauseIndex literalStart source)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    metadata.clause =
      positionedComplementClause positions sourceClauseIndex
        sourceLiteralIndex sourceLiteral := by
  induction source generalizing literalStart metadata with
  | nil =>
      simp [complementClauseMetadataFrom] at metadataMember
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · rw [complementClauseMetadataFrom, if_pos compatible]
          at metadataMember
        exact induction (literalStart + 1) metadataMember originEq
      · rw [complementClauseMetadataFrom, if_neg compatible]
          at metadataMember
        simp only [List.mem_cons] at metadataMember
        rcases metadataMember with metadataEq | metadataMember
        · subst metadata
          cases originEq
          rfl
        · exact induction (literalStart + 1) metadataMember originEq

/-- Every global metadata entry retains a genuine source clause. -/
theorem formulaClauseMetadata_source_mem {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata positions source) :
    (metadata.sourceClause, metadata.sourceClauseIndex) ∈
      source.clauses.zipIdx := by
  simp only [formulaClauseMetadata, List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨taggedSource, taggedSourceMember, metadataMember⟩
  unfold clauseMetadataFor at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    exact taggedSourceMember
  · have sourceEq := complementClauseMetadataFrom_source_eq
      positions taggedSource.1 taggedSource.2 0
      taggedSource.1.literals metadataMember
    simpa [sourceEq.1, sourceEq.2] using taggedSourceMember

/-- Every globally indexed complement clause names a genuine incompatible
literal occurrence of its retained source clause. -/
theorem formulaClauseMetadata_complement_valid {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    {sourceLiteralIndex : Nat}
    {sourceLiteral : PeriodicLiteral Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata positions source)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    (metadata.sourceClause, metadata.sourceClauseIndex) ∈
        source.clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx ∧
      sourceLiteral.value ≠ normalizedPolarity sourceLiteralIndex := by
  have sourceMember :=
    formulaClauseMetadata_source_mem positions source metadataMember
  simp only [formulaClauseMetadata, List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨taggedSource, taggedSourceMember, metadataMember⟩
  unfold clauseMetadataFor at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    contradiction
  · have valid := complementClauseMetadataFrom_complement_valid
      positions taggedSource.1 taggedSource.2 0
      taggedSource.1.literals metadataMember originEq
    have sourceEq := complementClauseMetadataFrom_source_eq
      positions taggedSource.1 taggedSource.2 0
      taggedSource.1.literals metadataMember
    simpa [sourceEq.1, sourceEq.2] using
      And.intro sourceMember valid

/-- A globally indexed complement origin carries its exact positioned
binary clause. -/
theorem formulaClauseMetadata_complement_clause_eq {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    {sourceLiteralIndex : Nat}
    {sourceLiteral : PeriodicLiteral Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata positions source)
    (originEq :
      metadata.origin = .complement sourceLiteralIndex sourceLiteral) :
    metadata.clause =
      positionedComplementClause positions metadata.sourceClauseIndex
        sourceLiteralIndex sourceLiteral := by
  simp only [formulaClauseMetadata, List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨taggedSource, _taggedSourceMember, metadataMember⟩
  unfold clauseMetadataFor at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    contradiction
  · have clauseEq := complementClauseMetadataFrom_complement_clause_eq
      positions taggedSource.1 taggedSource.2 0
      taggedSource.1.literals metadataMember originEq
    have sourceEq := complementClauseMetadataFrom_source_eq
      positions taggedSource.1 taggedSource.2 0
      taggedSource.1.literals metadataMember
    simpa [sourceEq.2] using clauseEq

/-- A globally indexed normalized origin is exactly the main clause of its
retained source block. -/
theorem formulaClauseMetadata_normalized_clause_eq {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {metadata : ClauseMetadata Variable}
    (metadataMember : metadata ∈ formulaClauseMetadata positions source)
    (originEq : metadata.origin = .normalized) :
    metadata.clause =
      normalizedClause metadata.sourceClauseIndex metadata.sourceClause := by
  simp only [formulaClauseMetadata, List.mem_flatMap] at metadataMember
  rcases metadataMember with
    ⟨taggedSource, _taggedSourceMember, metadataMember⟩
  unfold clauseMetadataFor at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    rfl
  · exact
      (complementClauseMetadataFrom_origin_ne_normalized
        positions taggedSource.1 taggedSource.2 0
        taggedSource.1.literals metadataMember originEq).elim

/-- Looking up a genuine flattened output clause yields metadata carrying
that exact clause. -/
theorem formulaClauseMetadata_lookup {Variable : Type*}
    (positions : Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula positions source).clauses.zipIdx) :
    ∃ metadata,
      (formulaClauseMetadata positions source)[clauseIndex]? =
        some metadata ∧
      metadata.clause = clause := by
  have clauseLookup :
      (formula positions source).clauses[clauseIndex]? = some clause :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  have projectedLookup :
      ((formulaClauseMetadata positions source).map
          ClauseMetadata.clause)[clauseIndex]? = some clause := by
    simpa using clauseLookup
  rw [List.getElem?_map] at projectedLookup
  simpa only [Option.map_eq_some_iff] using projectedLookup

end PeriodicOneInThreePolarityNormalizationPositioned
end LeanTrominoes
