/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertexSeparation
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership
import LeanTrominoes.PositionedPeriodicCNFVariableVertexPosition

/-!
# Injectivity of polarity-normalization vertex positions

The logical normalization only emits a fresh variable when its occurrence
tag names a genuine incompatible source literal.  Recovering that provenance
from the flattened output occurrence list lets the geometric separation
lemmas prove injectivity of the final variable-position prefix.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- A fresh atom occurring in the normalized formula retains a genuine
incompatible source-clause and source-literal occurrence. -/
theorem normalizedFreshOccurrence_valid
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (fresh : FreshOccurrence Variable)
    (freshMember :
      Sum.inr fresh ∈
        PeriodicCNF.variableOccurrences
          (PeriodicOneInThreePolarityNormalization.formula source)) :
    ∃ sourceClause : PeriodicClause Variable,
      (sourceClause, fresh.1.1) ∈ source.clauses.zipIdx ∧
      (fresh.2, fresh.1.2) ∈ sourceClause.zipIdx ∧
      fresh.2.value ≠ normalizedPolarity fresh.1.2 := by
  change
    Sum.inr fresh ∈
      (source.clauses.zipIdx.flatMap fun taggedSource =>
        clauseClauses taggedSource.2 taggedSource.1).flatMap
          (fun clause => clause.map PeriodicLiteral.atom)
    at freshMember
  rw [List.mem_flatMap] at freshMember
  rcases freshMember with
    ⟨outputClause, outputClauseMember, freshAtomMember⟩
  rw [List.mem_flatMap] at outputClauseMember
  rcases outputClauseMember with
    ⟨taggedSource, taggedSourceMember, outputClauseMember⟩
  rcases taggedSource with ⟨sourceClause, sourceClauseIndex⟩
  simp only [clauseClauses, List.mem_cons] at outputClauseMember
  rcases outputClauseMember with normalizedEq | complementMember
  · subst outputClause
    simp only [normalizeClause, normalizeClauseFrom,
      List.map_map, Function.comp_def, List.mem_map]
      at freshAtomMember
    rcases freshAtomMember with
      ⟨⟨sourceLiteral, sourceLiteralIndex⟩,
        sourceLiteralMember, freshAtomEq⟩
    unfold normalizeLiteral at freshAtomEq
    split at freshAtomEq
    · simp [liftLiteral] at freshAtomEq
    · simp only [complementLiteral] at freshAtomEq
      have freshEq :
          ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) =
            fresh := by
        exact Sum.inr.inj freshAtomEq
      subst fresh
      exact ⟨sourceClause, taggedSourceMember,
        sourceLiteralMember, by assumption⟩
  · simp only [complementClauses, complementClausesFrom,
      List.mem_filterMap] at complementMember
    rcases complementMember with
      ⟨⟨sourceLiteral, sourceLiteralIndex⟩,
        sourceLiteralMember, outputClauseEq⟩
    split at outputClauseEq
    · contradiction
    · simp only [Option.some.injEq] at outputClauseEq
      subst outputClause
      simp only [complementClause, complementFalseLiteral,
        originalFalseLiteral, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false]
        at freshAtomMember
      rcases freshAtomMember with freshEq | impossible
      · have occurrenceEq :
            ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) =
              fresh :=
          Sum.inr.inj freshEq.symm
        subst fresh
        exact ⟨sourceClause, taggedSourceMember,
          sourceLiteralMember, by assumption⟩
      · contradiction

/-- An original atom occurring after route-subdivision normalization already
occurred in the refined source formula. -/
theorem originalOccurrence_mem_refinedSource
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {routes : PositionedPeriodicCNF.IncidenceRoutes}
    {atom : Variable}
    (atomMember :
      Sum.inl atom ∈
        (formula source sourcePlacement routes).erase.variableOccurrences) :
    atom ∈
      (refinedSource source sourcePlacement).erase.variableOccurrences := by
  have normalizedMember :
      Sum.inl atom ∈
        (PeriodicOneInThreePolarityNormalization.formula
          (refinedSource source sourcePlacement).erase).variableOccurrences := by
    simpa only [erase_formula,
      PeriodicCNF.variableOccurrences_variableGauge] using atomMember
  have positive :
      0 <
        ((PeriodicOneInThreePolarityNormalization.formula
          (refinedSource source sourcePlacement).erase).variableOccurrences
          ).count (Sum.inl atom) :=
    List.count_pos_iff.mpr normalizedMember
  rw [PeriodicOneInThreePolarityNormalization.formula_variableOccurrences_count_original]
    at positive
  exact List.count_pos_iff.mp positive

/-- A fresh atom occurring after route-subdivision normalization retains its
genuine refined-source occurrence tag. -/
theorem freshOccurrence_valid_of_final_member
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {routes : PositionedPeriodicCNF.IncidenceRoutes}
    {fresh : FreshOccurrence Variable}
    (freshMember :
      Sum.inr fresh ∈
        (formula source sourcePlacement routes).erase.variableOccurrences) :
    ∃ sourceClause : PositionedPeriodicClause Variable,
      (sourceClause, fresh.1.1) ∈
          (refinedSource source sourcePlacement).clauses.zipIdx ∧
      (fresh.2, fresh.1.2) ∈ sourceClause.literals.zipIdx ∧
      fresh.2.value ≠ normalizedPolarity fresh.1.2 := by
  have normalizedMember :
      Sum.inr fresh ∈
        (PeriodicOneInThreePolarityNormalization.formula
          (refinedSource source sourcePlacement).erase).variableOccurrences := by
    simpa only [erase_formula,
      PeriodicCNF.variableOccurrences_variableGauge] using freshMember
  rcases normalizedFreshOccurrence_valid
      (refinedSource source sourcePlacement).erase fresh normalizedMember with
    ⟨sourceLiterals, sourceClauseMember,
      sourceLiteralMember, incompatible⟩
  rw [PositionedPeriodicCNF.erase] at sourceClauseMember
  simp only [List.zipIdx_map, List.mem_map] at sourceClauseMember
  rcases sourceClauseMember with
    ⟨⟨sourceClause, sourceClauseIndex⟩,
      sourceClauseMember, taggedEq⟩
  have literalsEq : sourceClause.literals = sourceLiterals :=
    congrArg Prod.fst taggedEq
  have clauseIndexEq : sourceClauseIndex = fresh.1.1 :=
    congrArg Prod.snd taggedEq
  refine ⟨sourceClause, ?_, ?_, incompatible⟩
  · simpa only [clauseIndexEq] using sourceClauseMember
  · simpa only [literalsEq] using sourceLiteralMember

/-- Source-block and local-origin data uniquely name a generated normalized
clause. -/
def clauseMetadataKey
    {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable) :
    Nat × Option (Nat × PeriodicLiteral Variable) :=
  (metadata.sourceClauseIndex,
    match metadata.origin with
    | .normalized => none
    | .complement literalIndex literal => some (literalIndex, literal))

/-- Complement metadata projects to the same occurrence keys as the logical
fresh-variable enumeration. -/
theorem complementClauseMetadataFrom_keys
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (sourceClauseIndex literalStart : Nat)
    (source : PeriodicClause Variable) :
    (PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom
        positions sourceClause
          sourceClauseIndex literalStart source).map
        clauseMetadataKey =
      (freshVariablesFrom sourceClauseIndex literalStart source).map
        (fun fresh =>
          (fresh.1.1, some (fresh.1.2, fresh.2))) := by
  induction source generalizing literalStart with
  | nil => rfl
  | cons literal rest induction =>
      by_cases compatible :
          literal.value = normalizedPolarity literalStart
      · simp [PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom,
          freshVariablesFrom_cons, compatible,
          induction (literalStart + 1)]
      · simp [PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom,
          freshVariablesFrom_cons, compatible,
          clauseMetadataKey,
          induction (literalStart + 1)]

/-- The local normalized-main/complement origin keys do not repeat within
one source-clause replacement block. -/
theorem clauseMetadataFor_keys_nodup
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable) :
    ((PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor
        positions sourceClauseIndex sourceClause).map
      clauseMetadataKey).Nodup := by
  rw [PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor,
    List.map_cons, complementClauseMetadataFrom_keys]
  apply List.Nodup.cons
  · simp [clauseMetadataKey]
  · apply (freshVariablesFrom_nodup sourceClauseIndex 0
      sourceClause.literals).map
    intro first second keysEq
    rcases first with ⟨⟨firstClauseIndex, firstIndex⟩, firstLiteral⟩
    rcases second with
      ⟨⟨secondClauseIndex, secondIndex⟩, secondLiteral⟩
    simp only [Prod.mk.injEq, Option.some.injEq] at keysEq
    exact Prod.ext
      (Prod.ext keysEq.1 keysEq.2.1) keysEq.2.2

/-- Every local metadata entry retains the source index of its replacement
block. -/
theorem clauseMetadataFor_sourceIndex_eq
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PositionedPeriodicClause Variable)
    {metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable}
    (metadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor
          positions sourceClauseIndex sourceClause) :
    metadata.sourceClauseIndex = sourceClauseIndex := by
  unfold PeriodicOneInThreePolarityNormalizationPositioned.clauseMetadataFor
    at metadataMember
  simp only [List.mem_cons] at metadataMember
  rcases metadataMember with metadataEq | metadataMember
  · subst metadata
    rfl
  · exact
      (PeriodicOneInThreePolarityNormalizationPositioned.complementClauseMetadataFrom_source_eq
          positions sourceClause sourceClauseIndex 0
          sourceClause.literals metadataMember).2

/-- Origin keys are pairwise distinct across the complete flattened clause
metadata enumeration. -/
theorem formulaClauseMetadata_keys_nodup
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (source : PositionedPeriodicCNF Variable) :
    ((PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions source).map
      clauseMetadataKey).Nodup := by
  have sourceIndicesPairwise :
      source.clauses.zipIdx.Pairwise
        (fun first second => first.2 ≠ second.2) := by
    rw [← List.pairwise_map]
    exact List.nodup_zipIdx_map_snd source.clauses
  rw [PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata,
    List.map_flatMap, List.nodup_flatMap]
  constructor
  · intro taggedSource _
    exact clauseMetadataFor_keys_nodup
      positions taggedSource.2 taggedSource.1
  · exact sourceIndicesPairwise.imp fun
      {first second} sourceIndexNe => by
        change List.Disjoint _ _
        rw [List.disjoint_left]
        intro key firstKeyMember secondKeyMember
        rcases List.mem_map.mp firstKeyMember with
          ⟨firstMetadata, firstMetadataMember, firstKeyEq⟩
        rcases List.mem_map.mp secondKeyMember with
          ⟨secondMetadata, secondMetadataMember, secondKeyEq⟩
        have firstSourceEq := clauseMetadataFor_sourceIndex_eq
          positions first.2 first.1 firstMetadataMember
        have secondSourceEq := clauseMetadataFor_sourceIndex_eq
          positions second.2 second.1 secondMetadataMember
        apply sourceIndexNe
        have sourceKeysEq :=
          congrArg Prod.fst (firstKeyEq.trans secondKeyEq.symm)
        simpa [clauseMetadataKey,
          firstSourceEq, secondSourceEq] using sourceKeysEq

/-- Equal origin keys returned by two flattened metadata lookups identify
the same generated clause index. -/
theorem formulaClauseMetadata_lookup_key_injective
    {Variable : Type*}
    (positions :
      PeriodicOneInThreePolarityNormalizationPositioned.Positions Variable)
    (source : PositionedPeriodicCNF Variable)
    {firstMetadata secondMetadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable}
    {firstIndex secondIndex : Nat}
    (firstLookup :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions source)[firstIndex]? = some firstMetadata)
    (secondLookup :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        positions source)[secondIndex]? = some secondMetadata)
    (keysEq :
      clauseMetadataKey firstMetadata =
        clauseMetadataKey secondMetadata) :
    firstIndex = secondIndex := by
  have firstKeyLookup :
      ((PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          positions source).map
        clauseMetadataKey)[firstIndex]? =
        some (clauseMetadataKey firstMetadata) := by
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      ((PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          positions source).map
        clauseMetadataKey)[secondIndex]? =
        some (clauseMetadataKey secondMetadata) := by
    rw [List.getElem?_map, secondLookup]
    rfl
  rcases List.getElem?_eq_some_iff.mp firstKeyLookup with
    ⟨firstLt, firstAt⟩
  rcases List.getElem?_eq_some_iff.mp secondKeyLookup with
    ⟨secondLt, secondAt⟩
  apply
    ((formulaClauseMetadata_keys_nodup positions source).getElem_inj_iff
      (hi := firstLt) (hj := secondLt)).mp
  rw [firstAt, secondAt, keysEq]

/-- A final gauged clause lookup recovers the raw metadata entry at the same
flattened presentation index. -/
theorem exists_metadata_of_final_clause_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {finalClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {clauseIndex : Nat}
    (finalClauseMember :
      (finalClause, clauseIndex) ∈
        (formula source sourcePlacement routes).clauses.zipIdx) :
    ∃ metadata :
        PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
          Variable,
      (clauseMetadata source sourcePlacement routes)[clauseIndex]? =
          some metadata ∧
      metadata ∈ clauseMetadata source sourcePlacement routes ∧
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          (refinedSource source sourcePlacement).clauses.zipIdx ∧
      finalClause = variableGaugeClause freshGauge metadata.clause := by
  have gaugedMember :
      (finalClause, clauseIndex) ∈
        ((rawFormula source sourcePlacement routes).variableGauge
          freshGauge).clauses.zipIdx := by
    simpa only [formula] using finalClauseMember
  rcases
      PositionedPeriodicCNF.exists_sourceClause_of_variableGaugeClause_mem
        (rawFormula source sourcePlacement routes) freshGauge gaugedMember with
    ⟨rawClause, rawClauseMember, finalClauseEq⟩
  have formulaClauseMember :
      (rawClause, clauseIndex) ∈
        (PeriodicOneInThreePolarityNormalizationPositioned.formula
          (rawPositions sourcePlacement routes)
          (refinedSource source sourcePlacement)).clauses.zipIdx := by
    simpa only [rawFormula] using rawClauseMember
  rcases
      PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_lookup
          (rawPositions sourcePlacement routes)
          (refinedSource source sourcePlacement) formulaClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEq⟩
  have rawMetadataLookup :
      (clauseMetadata source sourcePlacement routes)[clauseIndex]? =
        some metadata := by
    simpa only [clauseMetadata] using metadataLookup
  have metadataIndexLt :
      clauseIndex <
        (clauseMetadata source sourcePlacement routes).length :=
    (List.getElem?_eq_some_iff.mp rawMetadataLookup).1
  have metadataAt :
      (clauseMetadata source sourcePlacement routes)[clauseIndex] =
        metadata :=
    (List.getElem?_eq_some_iff.mp rawMetadataLookup).2
  have metadataMember :
      metadata ∈ clauseMetadata source sourcePlacement routes := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have sourceClauseMember :=
    PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_source_mem
        (rawPositions sourcePlacement routes)
        (refinedSource source sourcePlacement)
        (by simpa only [clauseMetadata] using metadataMember)
  refine ⟨metadata, rawMetadataLookup, metadataMember,
    sourceClauseMember, ?_⟩
  rw [metadataClauseEq]
  simpa only [variableGaugeClause] using finalClauseEq

/-- A genuine positioned clause supplies its clause vertex in the finite
incidence graph. -/
theorem clauseVertex_mem_incidenceGraph_of_member
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    CNFVertex.clause clauseIndex ∈ source.erase.incidenceGraph.vertices := by
  change
    CNFVertex.clause clauseIndex ∈
      source.erase.incidenceVariableVertices ++
        PeriodicCNF.incidenceClauseVertices source.erase
  apply List.mem_append_right
  unfold PeriodicCNF.incidenceClauseVertices
  apply List.mem_map.mpr
  refine ⟨clauseIndex, ?_, rfl⟩
  simp only [List.mem_range]
  have clauseIndexLt : clauseIndex < source.clauses.length :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp clauseMember)).1
  simpa [PositionedPeriodicCNF.erase] using clauseIndexLt

/-- Refined source clauses have zero anchor, so their canonical incidence
position is their stored displayed position. -/
theorem refinedSource_canonicalClausePosition_eq_position
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    PositionedPeriodicCNF.canonicalClausePosition
        (refinedPlacement sourcePlacement) sourceClause =
      sourceClause.position := by
  rw [PositionedPeriodicCNF.canonicalClausePosition,
    refinedSource_clauseAnchor_eq_zero
      source sourcePlacement sourceClauseMember]
  simp [PeriodicVariablePlacement.translation, Cell.scale, Cell.sub]

/-- A genuine refined-source clause position occurs in the scaled source
drawing's vertex-position list. -/
theorem refinedClausePosition_mem_sourceVertices
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    sourceClause.position ∈
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (scaledSourcePresentation presentation).routes).vertexPositions := by
  have vertexMember :=
    clauseVertex_mem_incidenceGraph_of_member
      (refinedSource source sourcePlacement) sourceClauseMember
  have stored :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_mem_of_compatible
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation presentation).routes
      (scaledSourcePresentation presentation).compatible vertexMember
  rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement)
    (scaledSourcePresentation presentation).routes vertexMember] at stored
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  simpa [PositionedPeriodicCNF.incidenceVertexPositionAt,
    clauseLookup,
    refinedSource_canonicalClausePosition_eq_position
      source sourcePlacement sourceClauseMember] using stored

/-- Equality of genuine refined-source clause positions identifies their
presentation indices. -/
theorem refinedClausePosition_eq_imp_index_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstClause secondClause : PositionedPeriodicClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (positionsEq : firstClause.position = secondClause.position) :
    firstClauseIndex = secondClauseIndex := by
  have firstVertexMember :=
    clauseVertex_mem_incidenceGraph_of_member
      (refinedSource source sourcePlacement) firstMember
  have secondVertexMember :=
    clauseVertex_mem_incidenceGraph_of_member
      (refinedSource source sourcePlacement) secondMember
  have verticesEq :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_injective_on_of_compatible
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation presentation).routes
      (scaledSourcePresentation presentation).compatible
      firstVertexMember secondVertexMember (by
        rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes firstVertexMember,
          PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
            (refinedSource source sourcePlacement)
            (refinedPlacement sourcePlacement)
            (scaledSourcePresentation presentation).routes
            secondVertexMember]
        have firstLookup :=
          (List.mem_zipIdx_iff_getElem?).mp firstMember
        have secondLookup :=
          (List.mem_zipIdx_iff_getElem?).mp secondMember
        simpa [PositionedPeriodicCNF.incidenceVertexPositionAt,
          firstLookup, secondLookup,
          refinedSource_canonicalClausePosition_eq_position
            source sourcePlacement firstMember,
          refinedSource_canonicalClausePosition_eq_position
            source sourcePlacement secondMember] using positionsEq)
  exact CNFVertex.clause.inj verticesEq

/-- Equality of two genuine final canonical clause positions identifies their
flattened output-clause indices. -/
theorem finalCanonicalClausePosition_eq_imp_index_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstClause secondClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (formula source sourcePlacement presentation.routes).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (formula source sourcePlacement presentation.routes).clauses.zipIdx)
    (positionsEq :
      PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement presentation.routes) firstClause =
        PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement presentation.routes) secondClause) :
    firstClauseIndex = secondClauseIndex := by
  rcases exists_metadata_of_final_clause_member
      source sourcePlacement presentation.routes firstClauseMember with
    ⟨firstMetadata, firstLookup, firstMetadataMember,
      firstSourceMember, firstClauseEq⟩
  rcases exists_metadata_of_final_clause_member
      source sourcePlacement presentation.routes secondClauseMember with
    ⟨secondMetadata, secondLookup, secondMetadataMember,
      secondSourceMember, secondClauseEq⟩
  have firstBaseLookup :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement))[firstClauseIndex]? =
          some firstMetadata := by
    simpa only [clauseMetadata] using firstLookup
  have secondBaseLookup :
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement))[secondClauseIndex]? =
          some secondMetadata := by
    simpa only [clauseMetadata] using secondLookup
  have firstBaseMember :
      firstMetadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement) := by
    simpa only [clauseMetadata] using firstMetadataMember
  have secondBaseMember :
      secondMetadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement) := by
    simpa only [clauseMetadata] using secondMetadataMember
  cases firstOriginEq : firstMetadata.origin with
  | normalized =>
      have firstRawClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            firstBaseMember firstOriginEq
      have firstPositionEq :
          PositionedPeriodicCNF.canonicalClausePosition
              (placement sourcePlacement presentation.routes) firstClause =
            firstMetadata.sourceClause.position := by
        rw [firstClauseEq, firstRawClauseEq]
        exact canonicalClausePosition_normalized
          source sourcePlacement presentation.routes firstSourceMember
      cases secondOriginEq : secondMetadata.origin with
      | normalized =>
          have secondRawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondPositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  secondClause =
                secondMetadata.sourceClause.position := by
            rw [secondClauseEq, secondRawClauseEq]
            exact canonicalClausePosition_normalized
              source sourcePlacement presentation.routes secondSourceMember
          have sourceIndexEq :=
            refinedClausePosition_eq_imp_index_eq presentation
              firstSourceMember secondSourceMember
              (firstPositionEq.symm.trans
                (positionsEq.trans secondPositionEq))
          apply formulaClauseMetadata_lookup_key_injective
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            firstBaseLookup secondBaseLookup
          simp [clauseMetadataKey, firstOriginEq, secondOriginEq,
            sourceIndexEq]
      | complement secondLiteralIndex secondLiteral =>
          have secondValid :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondRawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondPositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  secondClause =
                routePoint presentation.routes
                  ((secondMetadata.sourceClauseIndex, secondLiteralIndex),
                    secondLiteral) 2 := by
            rw [secondClauseEq, secondRawClauseEq]
            exact canonicalClausePosition_complement
              sourcePlacement presentation.routes
              secondMetadata.sourceClauseIndex
              secondLiteralIndex secondLiteral
          have firstPositionMember :=
            refinedClausePosition_mem_sourceVertices
              presentation firstSourceMember
          exact
            ((sourceVertex_ne_routePoint presentation
              secondValid.1 secondValid.2.1 2 (Or.inr rfl)
              firstMetadata.sourceClause.position firstPositionMember)
              (firstPositionEq.symm.trans
                (positionsEq.trans secondPositionEq))).elim
  | complement firstLiteralIndex firstLiteral =>
      have firstValid :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            firstBaseMember firstOriginEq
      have firstRawClauseEq :=
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
            (rawPositions sourcePlacement presentation.routes)
            (refinedSource source sourcePlacement)
            firstBaseMember firstOriginEq
      have firstPositionEq :
          PositionedPeriodicCNF.canonicalClausePosition
              (placement sourcePlacement presentation.routes) firstClause =
            routePoint presentation.routes
              ((firstMetadata.sourceClauseIndex, firstLiteralIndex),
                firstLiteral) 2 := by
        rw [firstClauseEq, firstRawClauseEq]
        exact canonicalClausePosition_complement
          sourcePlacement presentation.routes
          firstMetadata.sourceClauseIndex firstLiteralIndex firstLiteral
      cases secondOriginEq : secondMetadata.origin with
      | normalized =>
          have secondRawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondPositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  secondClause =
                secondMetadata.sourceClause.position := by
            rw [secondClauseEq, secondRawClauseEq]
            exact canonicalClausePosition_normalized
              source sourcePlacement presentation.routes secondSourceMember
          have secondPositionMember :=
            refinedClausePosition_mem_sourceVertices
              presentation secondSourceMember
          exact
            ((sourceVertex_ne_routePoint presentation
              firstValid.1 firstValid.2.1 2 (Or.inr rfl)
              secondMetadata.sourceClause.position secondPositionMember)
              (secondPositionEq.symm.trans
                (positionsEq.symm.trans firstPositionEq))).elim
      | complement secondLiteralIndex secondLiteral =>
          have secondValid :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondRawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
                (rawPositions sourcePlacement presentation.routes)
                (refinedSource source sourcePlacement)
                secondBaseMember secondOriginEq
          have secondPositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  secondClause =
                routePoint presentation.routes
                  ((secondMetadata.sourceClauseIndex, secondLiteralIndex),
                    secondLiteral) 2 := by
            rw [secondClauseEq, secondRawClauseEq]
            exact canonicalClausePosition_complement
              sourcePlacement presentation.routes
              secondMetadata.sourceClauseIndex
              secondLiteralIndex secondLiteral
          by_cases occurrenceEq :
              ((firstMetadata.sourceClauseIndex, firstLiteralIndex),
                  firstLiteral) =
                ((secondMetadata.sourceClauseIndex, secondLiteralIndex),
                  secondLiteral)
          · apply formulaClauseMetadata_lookup_key_injective
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              firstBaseLookup secondBaseLookup
            have sourceIndexEq :=
              congrArg (fun occurrence => occurrence.1.1) occurrenceEq
            have literalIndexEq :=
              congrArg (fun occurrence => occurrence.1.2) occurrenceEq
            have literalEq :=
              congrArg (fun occurrence => occurrence.2) occurrenceEq
            simp only [clauseMetadataKey, firstOriginEq, secondOriginEq,
              Option.some.injEq, Prod.mk.injEq]
            exact ⟨sourceIndexEq, literalIndexEq, literalEq⟩
          · exact
              ((routePoint_ne_of_occurrence_ne presentation
                firstValid.1 secondValid.1
                firstValid.2.1 secondValid.2.1
                2 2 (Or.inr rfl) (Or.inr rfl) occurrenceEq)
                (firstPositionEq.symm.trans
                  (positionsEq.trans secondPositionEq))).elim

/-- The canonical clause-position suffix of the final normalized incidence
drawing contains no duplicates. -/
theorem finalCanonicalClausePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ((formula source sourcePlacement presentation.routes).clauses.map
      (PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement presentation.routes))).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro firstIndex secondIndex positionsEq
  apply Fin.ext
  apply finalCanonicalClausePosition_eq_imp_index_eq presentation
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by simpa using firstIndex.isLt)
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by simpa using secondIndex.isLt)
  · simpa using positionsEq

/-- An atom occurring in a positioned formula supplies its variable vertex
in the finite incidence graph. -/
theorem variableVertex_mem_incidenceGraph_of_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {atom : Variable}
    (atomMember : atom ∈ source.erase.variableOccurrences) :
    CNFVertex.variable atom ∈ source.erase.incidenceGraph.vertices := by
  change
    CNFVertex.variable atom ∈
      source.erase.incidenceVariableVertices ++
        PeriodicCNF.incidenceClauseVertices source.erase
  apply List.mem_append_left
  unfold PeriodicCNF.incidenceVariableVertices
  exact List.mem_map.mpr
    ⟨atom, List.mem_dedup.mpr atomMember, rfl⟩

/-- A genuine refined-source variable position occurs in the scaled source
drawing's complete vertex-position list. -/
theorem refinedVariablePosition_mem_sourceVertices
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {atom : Variable}
    (atomMember :
      atom ∈
        (refinedSource source sourcePlacement).erase.variableOccurrences) :
    (refinedPlacement sourcePlacement).position atom ∈
      (PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (scaledSourcePresentation presentation).routes).vertexPositions := by
  have vertexMember :=
    variableVertex_mem_incidenceGraph_of_occurrence
      (refinedSource source sourcePlacement) atomMember
  have stored :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_mem_of_compatible
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation presentation).routes
      (scaledSourcePresentation presentation).compatible vertexMember
  rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement)
    (scaledSourcePresentation presentation).routes vertexMember] at stored
  exact stored

/-- Distinct genuine original atoms retain distinct positions in the scaled
source drawing. -/
theorem refinedVariablePosition_eq_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {first second : Variable}
    (firstMember :
      first ∈
        (refinedSource source sourcePlacement).erase.variableOccurrences)
    (secondMember :
      second ∈
        (refinedSource source sourcePlacement).erase.variableOccurrences)
    (positionsEq :
      (refinedPlacement sourcePlacement).position first =
        (refinedPlacement sourcePlacement).position second) :
    first = second := by
  have firstVertexMember :=
    variableVertex_mem_incidenceGraph_of_occurrence
      (refinedSource source sourcePlacement) firstMember
  have secondVertexMember :=
    variableVertex_mem_incidenceGraph_of_occurrence
      (refinedSource source sourcePlacement) secondMember
  have verticesEq :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_injective_on_of_compatible
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation presentation).routes
      (scaledSourcePresentation presentation).compatible
      firstVertexMember secondVertexMember (by
        rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes firstVertexMember,
          PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
            (refinedSource source sourcePlacement)
            (refinedPlacement sourcePlacement)
            (scaledSourcePresentation presentation).routes
            secondVertexMember]
        exact positionsEq)
  cases verticesEq
  rfl

/-- On variables that genuinely occur in the normalized output, equality of
final prototype positions forces equality of the variables themselves. -/
theorem finalVariablePosition_eq_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {first second : PolarityNormalizedVariable Variable}
    (firstMember :
      first ∈
        PeriodicCNF.variableOccurrences
          (formula source sourcePlacement presentation.routes).erase)
    (secondMember :
      second ∈
        PeriodicCNF.variableOccurrences
          (formula source sourcePlacement presentation.routes).erase)
    (positionsEq :
      (placement sourcePlacement presentation.routes).position first =
        (placement sourcePlacement presentation.routes).position second) :
    first = second := by
  cases first with
  | inl firstAtom =>
      cases second with
      | inl secondAtom =>
          apply congrArg Sum.inl
          apply refinedVariablePosition_eq_imp_eq presentation
          · exact originalOccurrence_mem_refinedSource firstMember
          · exact originalOccurrence_mem_refinedSource secondMember
          · simpa only [placement_original_position] using positionsEq
      | inr secondFresh =>
          rcases freshOccurrence_valid_of_final_member secondMember with
            ⟨sourceClause, sourceClauseMember,
              sourceLiteralMember, _incompatible⟩
          have firstSourceMember :=
            originalOccurrence_mem_refinedSource firstMember
          have firstPositionMember :=
            refinedVariablePosition_mem_sourceVertices
              presentation firstSourceMember
          exact
            ((sourceVertex_ne_routePoint presentation
              sourceClauseMember sourceLiteralMember 1 (Or.inl rfl)
              ((refinedPlacement sourcePlacement).position firstAtom)
              firstPositionMember)
              (by simpa only [placement_original_position,
                placement_fresh_position] using positionsEq)).elim

  | inr firstFresh =>
      cases second with
      | inl secondAtom =>
          rcases freshOccurrence_valid_of_final_member firstMember with
            ⟨sourceClause, sourceClauseMember,
              sourceLiteralMember, _incompatible⟩
          have secondSourceMember :=
            originalOccurrence_mem_refinedSource secondMember
          have secondPositionMember :=
            refinedVariablePosition_mem_sourceVertices
              presentation secondSourceMember
          exact
            ((sourceVertex_ne_routePoint presentation
              sourceClauseMember sourceLiteralMember 1 (Or.inl rfl)
              ((refinedPlacement sourcePlacement).position secondAtom)
              secondPositionMember)
              (by simpa only [placement_original_position,
                placement_fresh_position] using positionsEq.symm)).elim
      | inr secondFresh =>
          by_cases freshEq : firstFresh = secondFresh
          · exact congrArg Sum.inr freshEq
          · rcases freshOccurrence_valid_of_final_member firstMember with
              ⟨firstClause, firstClauseMember,
                firstLiteralMember, _firstIncompatible⟩
            rcases freshOccurrence_valid_of_final_member secondMember with
              ⟨secondClause, secondClauseMember,
                secondLiteralMember, _secondIncompatible⟩
            exact
              ((routePoint_ne_of_occurrence_ne presentation
                firstClauseMember secondClauseMember
                firstLiteralMember secondLiteralMember
                1 1 (Or.inl rfl) (Or.inl rfl) freshEq)
                (by simpa only [placement_fresh_position]
                  using positionsEq)).elim

/-- The variable-position prefix of the final normalized incidence drawing
contains no duplicates. -/
theorem finalVariablePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    ((formula source sourcePlacement presentation.routes).erase.incidenceVariableVertices.map
        (PositionedPeriodicCNF.incidenceVariableVertexPosition
          (placement sourcePlacement presentation.routes))).Nodup := by
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map]
  apply
    (List.nodup_dedup
      (PeriodicCNF.variableOccurrences
        (formula source sourcePlacement presentation.routes).erase)).map_on
  intro first firstMember second secondMember positionsEq
  apply finalVariablePosition_eq_imp_eq presentation
  · exact List.mem_dedup.mp firstMember
  · exact List.mem_dedup.mp secondMember
  · simpa [PositionedPeriodicCNF.incidenceVariableVertexPosition,
      Function.comp_def] using positionsEq

/-- A genuine refined-source variable position differs from every genuine
refined-source clause position. -/
theorem refinedVariablePosition_ne_clausePosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {atom : Variable}
    (atomMember :
      atom ∈
        (refinedSource source sourcePlacement).erase.variableOccurrences)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx) :
    (refinedPlacement sourcePlacement).position atom ≠
      sourceClause.position := by
  have variableVertexMember :=
    variableVertex_mem_incidenceGraph_of_occurrence
      (refinedSource source sourcePlacement) atomMember
  have clauseVertexMember :=
    clauseVertex_mem_incidenceGraph_of_member
      (refinedSource source sourcePlacement) sourceClauseMember
  intro positionsEq
  have verticesEq :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_injective_on_of_compatible
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement)
      (scaledSourcePresentation presentation).routes
      (scaledSourcePresentation presentation).compatible
      variableVertexMember clauseVertexMember (by
        rw [PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes variableVertexMember,
          PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
            (refinedSource source sourcePlacement)
            (refinedPlacement sourcePlacement)
            (scaledSourcePresentation presentation).routes
            clauseVertexMember]
        have clauseLookup :=
          (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
        simpa [PositionedPeriodicCNF.incidenceVertexPositionAt,
          clauseLookup,
          refinedSource_canonicalClausePosition_eq_position
            source sourcePlacement sourceClauseMember] using positionsEq)
  cases verticesEq

/-- Every genuine final variable prototype differs from every genuine final
canonical clause prototype. -/
theorem finalVariablePosition_ne_canonicalClausePosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {atom : PolarityNormalizedVariable Variable}
    (atomMember :
      atom ∈ PeriodicCNF.variableOccurrences
        (formula source sourcePlacement presentation.routes).erase)
    {finalClause :
      PositionedPeriodicClause (PolarityNormalizedVariable Variable)}
    {finalClauseIndex : Nat}
    (finalClauseMember :
      (finalClause, finalClauseIndex) ∈
        (formula source sourcePlacement presentation.routes).clauses.zipIdx) :
    (placement sourcePlacement presentation.routes).position atom ≠
      PositionedPeriodicCNF.canonicalClausePosition
        (placement sourcePlacement presentation.routes) finalClause := by
  rcases exists_metadata_of_final_clause_member
      source sourcePlacement presentation.routes finalClauseMember with
    ⟨metadata, _metadataLookup, metadataMember,
      sourceClauseMember, finalClauseEq⟩
  have baseMetadataMember :
      metadata ∈
        PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement) := by
    simpa only [clauseMetadata] using metadataMember
  cases atom with
  | inl originalAtom =>
      have originalMember :=
        originalOccurrence_mem_refinedSource atomMember
      have originalPositionMember :=
        refinedVariablePosition_mem_sourceVertices
          presentation originalMember
      cases originEq : metadata.origin with
      | normalized =>
          have rawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have clausePositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  finalClause =
                metadata.sourceClause.position := by
            rw [finalClauseEq, rawClauseEq]
            exact canonicalClausePosition_normalized
              source sourcePlacement presentation.routes sourceClauseMember
          intro positionsEq
          exact
            refinedVariablePosition_ne_clausePosition presentation
              originalMember sourceClauseMember
              (by simpa only [placement_original_position,
                clausePositionEq] using positionsEq)
      | complement sourceLiteralIndex sourceLiteral =>
          have valid :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have rawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have clausePositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  finalClause =
                routePoint presentation.routes
                  ((metadata.sourceClauseIndex, sourceLiteralIndex),
                    sourceLiteral) 2 := by
            rw [finalClauseEq, rawClauseEq]
            exact canonicalClausePosition_complement
              sourcePlacement presentation.routes
              metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
          intro positionsEq
          exact
            sourceVertex_ne_routePoint presentation
              valid.1 valid.2.1 2 (Or.inr rfl)
              ((refinedPlacement sourcePlacement).position originalAtom)
              originalPositionMember
              (by simpa only [placement_original_position,
                clausePositionEq] using positionsEq)
  | inr fresh =>
      rcases freshOccurrence_valid_of_final_member atomMember with
        ⟨freshSourceClause, freshSourceClauseMember,
          freshSourceLiteralMember, _freshIncompatible⟩
      cases originEq : metadata.origin with
      | normalized =>
          have rawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_normalized_clause_eq
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have clausePositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  finalClause =
                metadata.sourceClause.position := by
            rw [finalClauseEq, rawClauseEq]
            exact canonicalClausePosition_normalized
              source sourcePlacement presentation.routes sourceClauseMember
          have clausePositionMember :=
            refinedClausePosition_mem_sourceVertices
              presentation sourceClauseMember
          intro positionsEq
          exact
            (sourceVertex_ne_routePoint presentation
              freshSourceClauseMember freshSourceLiteralMember
              1 (Or.inl rfl) metadata.sourceClause.position
              clausePositionMember)
              (by simpa only [placement_fresh_position,
                clausePositionEq] using positionsEq.symm)
      | complement sourceLiteralIndex sourceLiteral =>
          have valid :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have rawClauseEq :=
            PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_clause_eq
              (rawPositions sourcePlacement presentation.routes)
              (refinedSource source sourcePlacement)
              baseMetadataMember originEq
          have clausePositionEq :
              PositionedPeriodicCNF.canonicalClausePosition
                  (placement sourcePlacement presentation.routes)
                  finalClause =
                routePoint presentation.routes
                  ((metadata.sourceClauseIndex, sourceLiteralIndex),
                    sourceLiteral) 2 := by
            rw [finalClauseEq, rawClauseEq]
            exact canonicalClausePosition_complement
              sourcePlacement presentation.routes
              metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral
          by_cases occurrenceEq :
              fresh =
                ((metadata.sourceClauseIndex, sourceLiteralIndex),
                  sourceLiteral)
          · subst fresh
            intro positionsEq
            exact
              routePoint_one_ne_two presentation valid.1 valid.2.1
                (by simpa only [placement_fresh_position,
                  clausePositionEq] using positionsEq)
          · intro positionsEq
            exact
              routePoint_ne_of_occurrence_ne presentation
                freshSourceClauseMember valid.1
                freshSourceLiteralMember valid.2.1
                1 2 (Or.inl rfl) (Or.inr rfl) occurrenceEq
                (by simpa only [placement_fresh_position,
                  clausePositionEq] using positionsEq)

/-- The final variable-position prefix and canonical clause-position suffix
are disjoint. -/
theorem finalVariableClausePositions_disjoint
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    List.Disjoint
      ((formula source sourcePlacement presentation.routes).erase.incidenceVariableVertices.map
          (PositionedPeriodicCNF.incidenceVariableVertexPosition
            (placement sourcePlacement presentation.routes)))
      ((formula source sourcePlacement presentation.routes).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (placement sourcePlacement presentation.routes))) := by
  rw [List.disjoint_left]
  intro position variablePositionMember clausePositionMember
  rw [PeriodicCNF.incidenceVariableVertices, List.map_map,
    List.mem_map] at variablePositionMember
  rcases variablePositionMember with
    ⟨atom, atomMember, variablePositionEq⟩
  rw [List.mem_map] at clausePositionMember
  rcases clausePositionMember with
    ⟨finalClause, finalClauseMember, clausePositionEq⟩
  rcases List.mem_iff_getElem?.mp finalClauseMember with
    ⟨finalClauseIndex, finalClauseLookup⟩
  have indexedClauseMember :
      (finalClause, finalClauseIndex) ∈
        (formula source sourcePlacement presentation.routes).clauses.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr finalClauseLookup
  exact
    (finalVariablePosition_ne_canonicalClausePosition
      presentation (List.mem_dedup.mp atomMember) indexedClauseMember)
      (variablePositionEq.trans clausePositionEq.symm)

/-- All variable and clause prototype positions in the final normalized
incidence drawing are pairwise distinct. -/
theorem finalIncidenceVertexPositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (PositionedPeriodicCNF.incidenceVertexPositions
      (formula source sourcePlacement presentation.routes)
      (placement sourcePlacement presentation.routes)).Nodup := by
  rw [PositionedPeriodicCNF.incidenceVertexPositions_eq_variablePrefix_append]
  exact List.Nodup.append
    (finalVariablePositions_nodup presentation)
    (finalCanonicalClausePositions_nodup presentation)
    (finalVariableClausePositions_disjoint presentation)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
