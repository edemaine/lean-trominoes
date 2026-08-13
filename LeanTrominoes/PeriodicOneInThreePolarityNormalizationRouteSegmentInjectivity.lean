/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSegmentCoverage

/-!
# Injectivity of polarity-normalized segment provenance

The raw splitting operation partitions each refined source route into
disjoint occurrence ranges.  This file first recovers the unique refined
source incidence underlying every raw provenance entry, then uses the
partition ranges to show that no two raw occurrence keys collapse.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Retagging preserves the original occurrence and its source incidence
indices. -/
theorem exists_preserved_origin_of_mem_retagOrigins
    {origin : RawSegmentOrigin}
    {origins : List RawSegmentOrigin}
    {outputClauseIndex outputLiteralIndex : Nat}
    {fragment : RawRouteFragment}
    {latticeShift : Cell} {reversed : Bool}
    (originMember :
      origin ∈ retagOrigins outputClauseIndex outputLiteralIndex fragment
        latticeShift reversed origins) :
    ∃ sourceOrigin ∈ origins,
      origin.original = sourceOrigin.original ∧
      origin.sourceClauseIndex = sourceOrigin.sourceClauseIndex ∧
      origin.sourceLiteralIndex = sourceOrigin.sourceLiteralIndex := by
  simp only [retagOrigins, List.mem_map] at originMember
  rcases originMember with ⟨sourceOrigin, sourceOriginMember, originEq⟩
  subst origin
  exact ⟨sourceOrigin, sourceOriginMember, rfl, rfl, rfl⟩

/-- Fields of an unretagged source-origin entry are its declared route and
source incidence indices. -/
theorem sourceSegmentOrigin_source_fields
    {origin : RawSegmentOrigin}
    {routeIndex sourceClauseIndex sourceLiteralIndex : Nat}
    {route : List Cell}
    (originMember :
      origin ∈ sourceSegmentOrigins routeIndex sourceClauseIndex
        sourceLiteralIndex route) :
    origin.original.routeIndex = routeIndex ∧
      origin.sourceClauseIndex = sourceClauseIndex ∧
      origin.sourceLiteralIndex = sourceLiteralIndex := by
  simp only [sourceSegmentOrigins, List.mem_map] at originMember
  rcases originMember with ⟨taggedSegment, taggedSegmentMember, originEq⟩
  subst origin
  exact ⟨rfl, rfl, rfl⟩

/-- Retagged entries expose all output-side and geometric fields fixed by the
retagging operation. -/
theorem fields_of_mem_retagOrigins
    {origin : RawSegmentOrigin}
    {origins : List RawSegmentOrigin}
    {outputClauseIndex outputLiteralIndex : Nat}
    {fragment : RawRouteFragment}
    {latticeShift : Cell} {reversed : Bool}
    (originMember :
      origin ∈ retagOrigins outputClauseIndex outputLiteralIndex fragment
        latticeShift reversed origins) :
    origin.outputClauseIndex = outputClauseIndex ∧
      origin.outputLiteralIndex = outputLiteralIndex ∧
      origin.fragment = fragment ∧
      origin.latticeShift = latticeShift ∧
      origin.reversed = reversed := by
  simp only [retagOrigins, List.mem_map] at originMember
  rcases originMember with ⟨sourceOrigin, sourceOriginMember, originEq⟩
  subst origin
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every index emitted by `zipIdx` is at least its starting index. -/
theorem le_snd_of_mem_zipIdx_start
    {Value : Type*} {values : List Value} {start : Nat}
    {tagged : Value × Nat}
    (taggedMember : tagged ∈ values.zipIdx start) :
    start ≤ tagged.2 := by
  induction values generalizing start with
  | nil => simp at taggedMember
  | cons value rest induction =>
      simp only [List.zipIdx_cons, List.mem_cons] at taggedMember
      rcases taggedMember with taggedEq | taggedMember
      · subst tagged
        rfl
      · exact le_trans (Nat.le_succ start)
          (by simpa [Nat.add_comm] using
            (induction (start := start + 1) taggedMember))

/-- The unique entry in the first source-origin slot has segment index zero. -/
theorem sourceSegmentOrigin_segmentIndex_eq_zero_of_mem_take_one
    {origin : RawSegmentOrigin}
    {routeIndex sourceClauseIndex sourceLiteralIndex : Nat}
    {route : List Cell}
    (originMember :
      origin ∈ (sourceSegmentOrigins routeIndex sourceClauseIndex
        sourceLiteralIndex route).take 1) :
    origin.original.segmentIndex = 0 := by
  unfold sourceSegmentOrigins at originMember
  cases segmentsEq : gridPolylineSegments route with
  | nil => simp [segmentsEq] at originMember
  | cons segment rest =>
      simp [segmentsEq] at originMember
      subst origin
      rfl

/-- The unique source-origin slot after dropping the first has segment index
one. -/
theorem sourceSegmentOrigin_segmentIndex_eq_one_of_mem_drop_one_take_one
    {origin : RawSegmentOrigin}
    {routeIndex sourceClauseIndex sourceLiteralIndex : Nat}
    {route : List Cell}
    (originMember :
      origin ∈ ((sourceSegmentOrigins routeIndex sourceClauseIndex
        sourceLiteralIndex route).drop 1).take 1) :
    origin.original.segmentIndex = 1 := by
  unfold sourceSegmentOrigins at originMember
  cases segmentsEq : gridPolylineSegments route with
  | nil => simp [segmentsEq] at originMember
  | cons first rest =>
      cases rest with
      | nil => simp [segmentsEq] at originMember
      | cons second rest =>
          simp [segmentsEq] at originMember
          subst origin
          rfl

/-- Every source-origin entry after dropping two has segment index at least
two. -/
theorem sourceSegmentOrigin_segmentIndex_ge_two_of_mem_drop_two
    {origin : RawSegmentOrigin}
    {routeIndex sourceClauseIndex sourceLiteralIndex : Nat}
    {route : List Cell}
    (originMember :
      origin ∈ (sourceSegmentOrigins routeIndex sourceClauseIndex
        sourceLiteralIndex route).drop 2) :
    2 ≤ origin.original.segmentIndex := by
  unfold sourceSegmentOrigins at originMember
  cases segmentsEq : gridPolylineSegments route with
  | nil => simp [segmentsEq] at originMember
  | cons first rest =>
      cases rest with
      | nil => simp [segmentsEq] at originMember
      | cons second rest =>
          simp only [segmentsEq, List.zipIdx_cons, List.map_cons] at originMember
          rcases List.mem_map.mp originMember with
            ⟨taggedSegment, taggedSegmentMember, originEq⟩
          subst origin
          exact le_snd_of_mem_zipIdx_start taggedSegmentMember

/-- The four mutually exclusive shapes of a raw provenance entry. -/
inductive RawSegmentShape
    {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex : Nat)
    (origin : RawSegmentOrigin) : Prop where
  | wholeCase
      (metadataOrigin : metadata.origin = .normalized)
      (compatible : sourceLiteral.value =
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          sourceLiteralIndex)
      (outputLiteralIndex : origin.outputLiteralIndex = sourceLiteralIndex)
      (fragment : origin.fragment = .whole)
      (shift : origin.latticeShift = (0, 0))
      (reversed : origin.reversed = false) :
      RawSegmentShape metadata sourceLiteral sourceLiteralIndex origin
  | prefixCase
      (metadataOrigin : metadata.origin = .normalized)
      (incompatible : sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          sourceLiteralIndex)
      (outputLiteralIndex : origin.outputLiteralIndex = sourceLiteralIndex)
      (fragment : origin.fragment = .prefix)
      (shift : origin.latticeShift = (0, 0))
      (reversed : origin.reversed = false)
      (segmentIndex : origin.original.segmentIndex = 0) :
      RawSegmentShape metadata sourceLiteral sourceLiteralIndex origin
  | middleCase
      (metadataOrigin : metadata.origin =
        .complement sourceLiteralIndex sourceLiteral)
      (incompatible : sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          sourceLiteralIndex)
      (outputLiteralIndex : origin.outputLiteralIndex = 0)
      (fragment : origin.fragment = .middle)
      (shift : origin.latticeShift = complementLatticeShift sourceLiteral)
      (reversed : origin.reversed = true)
      (segmentIndex : origin.original.segmentIndex = 1) :
      RawSegmentShape metadata sourceLiteral sourceLiteralIndex origin
  | suffixCase
      (metadataOrigin : metadata.origin =
        .complement sourceLiteralIndex sourceLiteral)
      (incompatible : sourceLiteral.value ≠
        PeriodicOneInThreePolarityNormalization.normalizedPolarity
          sourceLiteralIndex)
      (outputLiteralIndex : origin.outputLiteralIndex = 1)
      (fragment : origin.fragment = .suffix)
      (shift : origin.latticeShift = complementLatticeShift sourceLiteral)
      (reversed : origin.reversed = false)
      (segmentIndex : 2 ≤ origin.original.segmentIndex) :
      RawSegmentShape metadata sourceLiteral sourceLiteralIndex origin

/-- A genuine raw provenance entry recovers source membership, its metadata
lookup, and exactly one of the four split shapes. -/
theorem rawSegmentOrigin_classify
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    {origin : RawSegmentOrigin}
    (originMember :
      origin ∈ rawSegmentOrigins source sourcePlacement presentation.routes
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex) :
    ∃ metadata sourceLiteral sourceLiteralIndex,
      (clauseMetadata source sourcePlacement presentation.routes)[taggedIncidence.1.clauseIndex]? =
        some metadata ∧
      (metadata.sourceClause, metadata.sourceClauseIndex) ∈
          (refinedSource source sourcePlacement).clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
          metadata.sourceClause.literals.zipIdx ∧
      origin.sourceClauseIndex = metadata.sourceClauseIndex ∧
      origin.sourceLiteralIndex = sourceLiteralIndex ∧
      origin.original.routeIndex =
        refinedIncidenceIndex source sourcePlacement metadata.sourceClause
          metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral ∧
      origin.outputClauseIndex = taggedIncidence.1.clauseIndex ∧
      origin.outputLiteralIndex = taggedIncidence.1.literalIndex ∧
      RawSegmentShape metadata sourceLiteral sourceLiteralIndex origin := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, originData⟩
  have metadataMember : metadata ∈
      clauseMetadata source sourcePlacement presentation.routes := by
    rcases List.getElem?_eq_some_iff.mp metadataLookup with
      ⟨metadataIndexLt, metadataAt⟩
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  rw [rawSegmentOrigins_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
    metadataLookup] at originMember
  let base := sourceSegmentOrigins
    (refinedIncidenceIndex source sourcePlacement metadata.sourceClause
      metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral)
    metadata.sourceClauseIndex sourceLiteralIndex
    (refinedRoute presentation.routes metadata.sourceClauseIndex
      sourceLiteralIndex)
  rcases originData with normalized | complement
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    subst sourceLiteralIndex
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
    by_cases compatible :
        sourceLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            taggedIncidence.1.literalIndex
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible, if_pos] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginMember
      have outputFields := fields_of_mem_retagOrigins originMember
      exact ⟨metadata, sourceLiteral, taggedIncidence.1.literalIndex,
        metadataLookup, sourceClauseMember, sourceLiteralMember,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2,
        (by rw [originalEq]; exact sourceFields.1),
        outputFields.1, outputFields.2.1,
        RawSegmentShape.wholeCase originEq compatible outputFields.2.1
          outputFields.2.2.1 outputFields.2.2.2.1
          outputFields.2.2.2.2⟩
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base :=
        List.mem_of_mem_take sourceOriginMember
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      have outputFields := fields_of_mem_retagOrigins originMember
      have segmentIndex :=
        sourceSegmentOrigin_segmentIndex_eq_zero_of_mem_take_one
          sourceOriginMember
      exact ⟨metadata, sourceLiteral, taggedIncidence.1.literalIndex,
        metadataLookup, sourceClauseMember, sourceLiteralMember,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2,
        (by rw [originalEq]; exact sourceFields.1),
        outputFields.1, outputFields.2.1,
        RawSegmentShape.prefixCase originEq compatible outputFields.2.1
          outputFields.2.2.1 outputFields.2.2.2.1
          outputFields.2.2.2.2 (by rw [originalEq]; exact segmentIndex)⟩
  · rcases complement with ⟨originEq, outputIndexCases⟩
    have incompatible :=
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement)
        (by simpa only [clauseMetadata] using metadataMember)
        originEq).2.2
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq, if_pos]
          at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base :=
        List.mem_of_mem_drop (List.mem_of_mem_take sourceOriginMember)
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      have outputFields := fields_of_mem_retagOrigins originMember
      have segmentIndex :=
        sourceSegmentOrigin_segmentIndex_eq_one_of_mem_drop_one_take_one
          sourceOriginMember
      exact ⟨metadata, sourceLiteral, sourceLiteralIndex,
        metadataLookup, sourceClauseMember, sourceLiteralMember,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2,
        (by rw [originalEq]; exact sourceFields.1),
        outputFields.1, outputFields.2.1.trans outputIndexEq.symm,
        RawSegmentShape.middleCase originEq incompatible outputFields.2.1
          outputFields.2.2.1 outputFields.2.2.2.1
          outputFields.2.2.2.2 (by rw [originalEq]; exact segmentIndex)⟩
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq,
        if_neg (by omega : (1 : Nat) ≠ 0), if_true] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base :=
        List.mem_of_mem_drop sourceOriginMember
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      have outputFields := fields_of_mem_retagOrigins originMember
      have segmentIndex :=
        sourceSegmentOrigin_segmentIndex_ge_two_of_mem_drop_two
          sourceOriginMember
      exact ⟨metadata, sourceLiteral, sourceLiteralIndex,
        metadataLookup, sourceClauseMember, sourceLiteralMember,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2,
        (by rw [originalEq]; exact sourceFields.1),
        outputFields.1, outputFields.2.1.trans outputIndexEq.symm,
        RawSegmentShape.suffixCase originEq incompatible outputFields.2.1
          outputFields.2.2.1 outputFields.2.2.2.1
          outputFields.2.2.2.2 (by rw [originalEq]; exact segmentIndex)⟩

/-- Original occurrences in one full source-origin table are duplicate-free. -/
theorem sourceSegmentOrigins_original_nodup
    (routeIndex sourceClauseIndex sourceLiteralIndex : Nat)
    (route : List Cell) :
    ((sourceSegmentOrigins routeIndex sourceClauseIndex sourceLiteralIndex
      route).map RawSegmentOrigin.original).Nodup := by
  unfold sourceSegmentOrigins
  rw [List.map_map]
  have taggedNodup : (gridPolylineSegments route).zipIdx.Nodup :=
    (List.nodup_zipIdx_map_snd (gridPolylineSegments route)).of_map
  apply taggedNodup.map_on
  intro first firstMember second secondMember originsEq
  have segmentIndexEq := congrArg IndexedGridSegment.segmentIndex originsEq
  exact PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
    firstMember secondMember segmentIndexEq

/-- Retagging any selection with duplicate-free original occurrences remains
duplicate-free as a provenance list. -/
theorem retagOrigins_nodup_of_original_nodup
    (outputClauseIndex outputLiteralIndex : Nat)
    (fragment : RawRouteFragment)
    (latticeShift : Cell) (reversed : Bool)
    (origins : List RawSegmentOrigin)
    (originalsNodup :
      (origins.map RawSegmentOrigin.original).Nodup) :
    (retagOrigins outputClauseIndex outputLiteralIndex fragment
      latticeShift reversed origins).Nodup := by
  have mappedNodup :
      ((retagOrigins outputClauseIndex outputLiteralIndex fragment
        latticeShift reversed origins).map
          RawSegmentOrigin.original).Nodup := by
    rw [retagOrigins_map_original]
    exact originalsNodup
  exact mappedNodup.of_map

private theorem nodup_take_local
    {Value : Type*} {values : List Value}
    (nodup : values.Nodup) (count : Nat) :
    (values.take count).Nodup := by
  change List.Pairwise (fun first second : Value => first ≠ second)
    (values.take count)
  exact List.Pairwise.take nodup

private theorem nodup_drop_local
    {Value : Type*} {values : List Value}
    (nodup : values.Nodup) (count : Nat) :
    (values.drop count).Nodup := by
  change List.Pairwise (fun first second : Value => first ≠ second)
    (values.drop count)
  exact List.Pairwise.drop nodup

/-- The provenance list of every genuine raw incidence has no duplicate
entries. -/
theorem rawSegmentOrigins_nodup_of_tagged
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx) :
    (rawSegmentOrigins source sourcePlacement presentation.routes
      taggedIncidence.1.clauseIndex
      taggedIncidence.1.literalIndex).Nodup := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, originData⟩
  rw [rawSegmentOrigins_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
    metadataLookup]
  let base := sourceSegmentOrigins
    (refinedIncidenceIndex source sourcePlacement metadata.sourceClause
      metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral)
    metadata.sourceClauseIndex sourceLiteralIndex
    (refinedRoute presentation.routes metadata.sourceClauseIndex
      sourceLiteralIndex)
  have baseOriginalsNodup :
      (base.map RawSegmentOrigin.original).Nodup :=
    sourceSegmentOrigins_original_nodup _ _ _ _
  rcases originData with normalized | complement
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    subst sourceLiteralIndex
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
    by_cases compatible :
        sourceLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            taggedIncidence.1.literalIndex
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible, if_pos]
      apply retagOrigins_nodup_of_original_nodup
      simpa [base] using baseOriginalsNodup
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible]
      apply retagOrigins_nodup_of_original_nodup
      simpa only [base, List.map_take] using
        nodup_take_local baseOriginalsNodup 1
  · rcases complement with ⟨originEq, outputIndexCases⟩
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · rw [outputIndexEq]
      simp only [rawSegmentOriginsForMetadata, originEq, if_pos]
      apply retagOrigins_nodup_of_original_nodup
      simpa only [base, List.map_take, List.map_drop] using
        nodup_take_local (nodup_drop_local baseOriginalsNodup 1) 1
    · rw [outputIndexEq]
      simp only [rawSegmentOriginsForMetadata, originEq,
        if_neg (by omega : (1 : Nat) ≠ 0), if_true]
      apply retagOrigins_nodup_of_original_nodup
      simpa only [base, List.map_drop] using
        nodup_drop_local baseOriginalsNodup 2

private theorem rawSegmentOrigin_eq_of_fields
    {first second : RawSegmentOrigin}
    (original : first.original = second.original)
    (latticeShift : first.latticeShift = second.latticeShift)
    (reversed : first.reversed = second.reversed)
    (sourceClauseIndex :
      first.sourceClauseIndex = second.sourceClauseIndex)
    (sourceLiteralIndex :
      first.sourceLiteralIndex = second.sourceLiteralIndex)
    (outputClauseIndex :
      first.outputClauseIndex = second.outputClauseIndex)
    (outputLiteralIndex :
      first.outputLiteralIndex = second.outputLiteralIndex)
    (fragment : first.fragment = second.fragment) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Equality of refined-source occurrences identifies the complete raw route
and within-route provenance occurrences that use them. -/
theorem rawSegmentOrigins_global_injective
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstIncidence secondIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (firstIncidenceMember :
      firstIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    {firstTaggedOrigin secondTaggedOrigin : RawSegmentOrigin × Nat}
    (firstOriginMember :
      firstTaggedOrigin ∈
        (rawSegmentOrigins source sourcePlacement presentation.routes
          firstIncidence.1.clauseIndex
          firstIncidence.1.literalIndex).zipIdx)
    (secondOriginMember :
      secondTaggedOrigin ∈
        (rawSegmentOrigins source sourcePlacement presentation.routes
          secondIncidence.1.clauseIndex
          secondIncidence.1.literalIndex).zipIdx)
    (originalEq :
      firstTaggedOrigin.1.original = secondTaggedOrigin.1.original) :
    firstIncidence = secondIncidence ∧
      firstTaggedOrigin = secondTaggedOrigin := by
  have firstOriginValueMember :=
    List.fst_mem_of_mem_zipIdx firstOriginMember
  have secondOriginValueMember :=
    List.fst_mem_of_mem_zipIdx secondOriginMember
  rcases rawSegmentOrigin_classify presentation firstIncidenceMember
      firstOriginValueMember with
    ⟨firstMetadata, firstLiteral, firstLiteralIndex,
      firstMetadataLookup, firstClauseMember, firstLiteralMember,
      firstSourceClauseField, firstSourceLiteralField,
      firstSourceRouteField,
      firstOutputClauseField, firstOutputLiteralField, firstShape⟩
  rcases rawSegmentOrigin_classify presentation secondIncidenceMember
      secondOriginValueMember with
    ⟨secondMetadata, secondLiteral, secondLiteralIndex,
      secondMetadataLookup, secondClauseMember, secondLiteralMember,
      secondSourceClauseField, secondSourceLiteralField,
      secondSourceRouteField,
      secondOutputClauseField, secondOutputLiteralField, secondShape⟩
  have sourceRouteIndexEq :
      refinedIncidenceIndex source sourcePlacement firstMetadata.sourceClause
          firstMetadata.sourceClauseIndex firstLiteralIndex firstLiteral =
        refinedIncidenceIndex source sourcePlacement secondMetadata.sourceClause
          secondMetadata.sourceClauseIndex secondLiteralIndex secondLiteral := by
    rw [← firstSourceRouteField, ← secondSourceRouteField, originalEq]
  have firstSourceTaggedMember := refinedIncidenceIndex_tagged_mem
    firstClauseMember firstLiteralMember
  have secondSourceTaggedMember := refinedIncidenceIndex_tagged_mem
    secondClauseMember secondLiteralMember
  have sourceTaggedEq :=
    PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
      firstSourceTaggedMember secondSourceTaggedMember sourceRouteIndexEq
  have sourceIncidenceEq := congrArg Prod.fst sourceTaggedEq
  have sourceFieldsEq :
      firstTaggedOrigin.1.sourceClauseIndex =
          secondTaggedOrigin.1.sourceClauseIndex ∧
        firstTaggedOrigin.1.sourceLiteralIndex =
          secondTaggedOrigin.1.sourceLiteralIndex := by
    constructor
    · exact firstSourceClauseField.trans
        ((congrArg CNFIncidence.clauseIndex sourceIncidenceEq).trans
          secondSourceClauseField.symm)
    · exact firstSourceLiteralField.trans
        ((congrArg CNFIncidence.literalIndex sourceIncidenceEq).trans
          secondSourceLiteralField.symm)
  have sourceClauseIndexEq :
      firstMetadata.sourceClauseIndex = secondMetadata.sourceClauseIndex :=
    firstSourceClauseField.symm.trans
      (sourceFieldsEq.1.trans secondSourceClauseField)
  have taggedClauseEq :=
    PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
      firstClauseMember secondClauseMember sourceClauseIndexEq
  have sourceClauseEq :
      firstMetadata.sourceClause = secondMetadata.sourceClause :=
    congrArg Prod.fst taggedClauseEq
  have sourceLiteralIndexEq : firstLiteralIndex = secondLiteralIndex :=
    firstSourceLiteralField.symm.trans
      (sourceFieldsEq.2.trans secondSourceLiteralField)
  have secondLiteralMember' :
      (secondLiteral, secondLiteralIndex) ∈
        firstMetadata.sourceClause.literals.zipIdx := by
    rw [sourceClauseEq]
    exact secondLiteralMember
  have taggedLiteralEq :=
    PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
      firstLiteralMember secondLiteralMember' sourceLiteralIndexEq
  have sourceLiteralEq : firstLiteral = secondLiteral :=
    congrArg Prod.fst taggedLiteralEq
  have compatibleIff :
      firstLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            firstLiteralIndex ↔
        secondLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            secondLiteralIndex := by
    rw [sourceLiteralEq, sourceLiteralIndexEq]
  have sourceSegmentIndexEq :
      firstTaggedOrigin.1.original.segmentIndex =
        secondTaggedOrigin.1.original.segmentIndex :=
    congrArg IndexedGridSegment.segmentIndex originalEq
  have finish
      (metadataKeysEq :
        PeriodicOneInThreePolarityNormalizationRouteSubdivision.clauseMetadataKey
            firstMetadata =
          PeriodicOneInThreePolarityNormalizationRouteSubdivision.clauseMetadataKey
            secondMetadata)
      (outputLiteralIndexEq :
        firstTaggedOrigin.1.outputLiteralIndex =
          secondTaggedOrigin.1.outputLiteralIndex)
      (fragmentEq :
        firstTaggedOrigin.1.fragment = secondTaggedOrigin.1.fragment)
      (shiftEq :
        firstTaggedOrigin.1.latticeShift =
          secondTaggedOrigin.1.latticeShift)
      (reversedEq :
        firstTaggedOrigin.1.reversed = secondTaggedOrigin.1.reversed) :
      firstIncidence = secondIncidence ∧
        firstTaggedOrigin = secondTaggedOrigin := by
    have firstBaseLookup :
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement))[
            firstIncidence.1.clauseIndex]? = some firstMetadata := by
      simpa only [clauseMetadata] using firstMetadataLookup
    have secondBaseLookup :
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement))[
            secondIncidence.1.clauseIndex]? = some secondMetadata := by
      simpa only [clauseMetadata] using secondMetadataLookup
    have outputClauseIndexEq :
        firstIncidence.1.clauseIndex = secondIncidence.1.clauseIndex :=
      formulaClauseMetadata_lookup_key_injective
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement)
        firstBaseLookup secondBaseLookup metadataKeysEq
    have rawIncidenceEq : firstIncidence.1 = secondIncidence.1 :=
      PeriodicCNF.incidence_eq_of_indices_eq
        (rawFormula source sourcePlacement presentation.routes).erase
        (List.fst_mem_of_mem_zipIdx firstIncidenceMember)
        (List.fst_mem_of_mem_zipIdx secondIncidenceMember)
        outputClauseIndexEq
        (firstOutputLiteralField.symm.trans
          (outputLiteralIndexEq.trans secondOutputLiteralField))
    have taggedIncidenceEq : firstIncidence = secondIncidence :=
      PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
        (PeriodicCNF.incidencesWithMetadata_nodup
          (rawFormula source sourcePlacement presentation.routes).erase)
        firstIncidenceMember secondIncidenceMember rawIncidenceEq
    have originEq : firstTaggedOrigin.1 = secondTaggedOrigin.1 := by
      exact rawSegmentOrigin_eq_of_fields originalEq shiftEq reversedEq
        sourceFieldsEq.1 sourceFieldsEq.2
        (firstOutputClauseField.trans
          (outputClauseIndexEq.trans secondOutputClauseField.symm))
        outputLiteralIndexEq fragmentEq
    subst secondIncidence
    have taggedOriginEq : firstTaggedOrigin = secondTaggedOrigin :=
      PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
        (rawSegmentOrigins_nodup_of_tagged presentation
          firstIncidenceMember)
        firstOriginMember secondOriginMember originEq
    exact ⟨rfl, taggedOriginEq⟩
  cases firstShape with
  | wholeCase firstMetadataOrigin firstCompatible firstOutputLiteral
      firstFragment firstShift firstReversed =>
      cases secondShape with
      | wholeCase secondMetadataOrigin secondCompatible secondOutputLiteral
          secondFragment secondShift secondReversed =>
          apply finish
          · simp [clauseMetadataKey, firstMetadataOrigin,
              secondMetadataOrigin, sourceClauseIndexEq]
          · exact firstOutputLiteral.trans
              (sourceLiteralIndexEq.trans secondOutputLiteral.symm)
          · exact firstFragment.trans secondFragment.symm
          · exact firstShift.trans secondShift.symm
          · exact firstReversed.trans secondReversed.symm
      | prefixCase _ secondIncompatible _ _ _ _ _ =>
          exact (secondIncompatible (compatibleIff.mp firstCompatible)).elim
      | middleCase _ secondIncompatible _ _ _ _ _ =>
          exact (secondIncompatible (compatibleIff.mp firstCompatible)).elim
      | suffixCase _ secondIncompatible _ _ _ _ _ =>
          exact (secondIncompatible (compatibleIff.mp firstCompatible)).elim
  | prefixCase firstMetadataOrigin firstIncompatible firstOutputLiteral
      firstFragment firstShift firstReversed firstSegmentIndex =>
      cases secondShape with
      | wholeCase _ secondCompatible _ _ _ _ =>
          exact (firstIncompatible (compatibleIff.mpr secondCompatible)).elim
      | prefixCase secondMetadataOrigin secondIncompatible secondOutputLiteral
          secondFragment secondShift secondReversed secondSegmentIndex =>
          apply finish
          · simp [clauseMetadataKey, firstMetadataOrigin,
              secondMetadataOrigin, sourceClauseIndexEq]
          · exact firstOutputLiteral.trans
              (sourceLiteralIndexEq.trans secondOutputLiteral.symm)
          · exact firstFragment.trans secondFragment.symm
          · exact firstShift.trans secondShift.symm
          · exact firstReversed.trans secondReversed.symm
      | middleCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
      | suffixCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
  | middleCase firstMetadataOrigin firstIncompatible firstOutputLiteral
      firstFragment firstShift firstReversed firstSegmentIndex =>
      cases secondShape with
      | wholeCase _ secondCompatible _ _ _ _ =>
          exact (firstIncompatible (compatibleIff.mpr secondCompatible)).elim
      | prefixCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
      | middleCase secondMetadataOrigin secondIncompatible secondOutputLiteral
          secondFragment secondShift secondReversed secondSegmentIndex =>
          apply finish
          · simp [clauseMetadataKey, firstMetadataOrigin,
              secondMetadataOrigin, sourceClauseIndexEq,
              sourceLiteralIndexEq, sourceLiteralEq]
          · exact firstOutputLiteral.trans secondOutputLiteral.symm
          · exact firstFragment.trans secondFragment.symm
          · have firstShift' := firstShift
            rw [sourceLiteralEq] at firstShift'
            exact firstShift'.trans secondShift.symm
          · exact firstReversed.trans secondReversed.symm
      | suffixCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
  | suffixCase firstMetadataOrigin firstIncompatible firstOutputLiteral
      firstFragment firstShift firstReversed firstSegmentIndex =>
      cases secondShape with
      | wholeCase _ secondCompatible _ _ _ _ =>
          exact (firstIncompatible (compatibleIff.mpr secondCompatible)).elim
      | prefixCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
      | middleCase _ _ _ _ _ _ secondSegmentIndex =>
          omega
      | suffixCase secondMetadataOrigin secondIncompatible secondOutputLiteral
          secondFragment secondShift secondReversed secondSegmentIndex =>
          apply finish
          · simp [clauseMetadataKey, firstMetadataOrigin,
              secondMetadataOrigin, sourceClauseIndexEq,
              sourceLiteralIndexEq, sourceLiteralEq]
          · exact firstOutputLiteral.trans secondOutputLiteral.symm
          · exact firstFragment.trans secondFragment.symm
          · have firstShift' := firstShift
            rw [sourceLiteralEq] at firstShift'
            exact firstShift'.trans secondShift.symm
          · exact firstReversed.trans secondReversed.symm

/-- Every genuine raw provenance entry has an underlying entry in the full
unretagged table of one genuine refined-source incidence. -/
theorem rawSegmentOrigin_exists_source_origin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (taggedIncidenceMember :
      taggedIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    {origin : RawSegmentOrigin}
    (originMember :
      origin ∈ rawSegmentOrigins source sourcePlacement presentation.routes
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex) :
    ∃ sourceClause sourceLiteral sourceClauseIndex sourceLiteralIndex,
      (sourceClause, sourceClauseIndex) ∈
          (refinedSource source sourcePlacement).clauses.zipIdx ∧
      (sourceLiteral, sourceLiteralIndex) ∈
          sourceClause.literals.zipIdx ∧
      ∃ sourceOrigin ∈ sourceSegmentOrigins
          (refinedIncidenceIndex source sourcePlacement sourceClause
            sourceClauseIndex sourceLiteralIndex sourceLiteral)
          sourceClauseIndex sourceLiteralIndex
          (refinedRoute presentation.routes sourceClauseIndex
            sourceLiteralIndex),
        origin.original = sourceOrigin.original ∧
        origin.sourceClauseIndex = sourceClauseIndex ∧
        origin.sourceLiteralIndex = sourceLiteralIndex := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, originData⟩
  rw [rawSegmentOrigins_of_metadata_lookup
    source sourcePlacement presentation.routes metadata
    taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
    metadataLookup] at originMember
  let base := sourceSegmentOrigins
    (refinedIncidenceIndex source sourcePlacement metadata.sourceClause
      metadata.sourceClauseIndex sourceLiteralIndex sourceLiteral)
    metadata.sourceClauseIndex sourceLiteralIndex
    (refinedRoute presentation.routes metadata.sourceClauseIndex
      sourceLiteralIndex)
  have finish {selected : List RawSegmentOrigin}
      (selectedSubset : ∀ {item}, item ∈ selected → item ∈ base)
      (selectedMember : origin ∈
        retagOrigins taggedIncidence.1.clauseIndex
          taggedIncidence.1.literalIndex origin.fragment
          origin.latticeShift origin.reversed selected) :
      ∃ sourceOrigin ∈ base,
        origin.original = sourceOrigin.original ∧
        origin.sourceClauseIndex = metadata.sourceClauseIndex ∧
        origin.sourceLiteralIndex = sourceLiteralIndex := by
    rcases exists_preserved_origin_of_mem_retagOrigins selectedMember with
      ⟨sourceOrigin, sourceOriginMember, originalEq,
        sourceClauseIndexEq, sourceLiteralIndexEq⟩
    have sourceOriginBaseMember := selectedSubset sourceOriginMember
    have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
    exact ⟨sourceOrigin, sourceOriginBaseMember, originalEq,
      sourceClauseIndexEq.trans sourceFields.2.1,
      sourceLiteralIndexEq.trans sourceFields.2.2⟩
  rcases originData with normalized | complement
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    subst sourceLiteralIndex
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
    by_cases compatible :
        sourceLiteral.value =
          PeriodicOneInThreePolarityNormalization.normalizedPolarity
            taggedIncidence.1.literalIndex
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible, if_pos] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginMember
      exact ⟨metadata.sourceClause, sourceLiteral,
        metadata.sourceClauseIndex, taggedIncidence.1.literalIndex,
        sourceClauseMember, sourceLiteralMember, sourceOrigin,
        sourceOriginMember, originalEq,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2⟩
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base := by
        exact List.mem_of_mem_take sourceOriginMember
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      exact ⟨metadata.sourceClause, sourceLiteral,
        metadata.sourceClauseIndex, taggedIncidence.1.literalIndex,
        sourceClauseMember, sourceLiteralMember, sourceOrigin,
        sourceOriginBaseMember, originalEq,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2⟩
  · rcases complement with ⟨originEq, outputIndexCases⟩
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq, if_pos]
          at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base :=
        List.mem_of_mem_drop (List.mem_of_mem_take sourceOriginMember)
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      exact ⟨metadata.sourceClause, sourceLiteral,
        metadata.sourceClauseIndex, sourceLiteralIndex,
        sourceClauseMember, sourceLiteralMember, sourceOrigin,
        sourceOriginBaseMember, originalEq,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2⟩
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq,
        if_neg (by omega : (1 : Nat) ≠ 0), if_true] at originMember
      rcases exists_preserved_origin_of_mem_retagOrigins originMember with
        ⟨sourceOrigin, sourceOriginMember, originalEq,
          sourceClauseIndexEq, sourceLiteralIndexEq⟩
      have sourceOriginBaseMember : sourceOrigin ∈ base :=
        List.mem_of_mem_drop sourceOriginMember
      have sourceFields := sourceSegmentOrigin_source_fields sourceOriginBaseMember
      exact ⟨metadata.sourceClause, sourceLiteral,
        metadata.sourceClauseIndex, sourceLiteralIndex,
        sourceClauseMember, sourceLiteralMember, sourceOrigin,
        sourceOriginBaseMember, originalEq,
        sourceClauseIndexEq.trans sourceFields.2.1,
        sourceLiteralIndexEq.trans sourceFields.2.2⟩

/-- Equal original occurrences force equality of the stored source
clause/literal indices of two genuine raw provenance entries. -/
theorem rawSegmentOrigin_source_indices_eq_of_original_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstIncidence secondIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (firstIncidenceMember :
      firstIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    (secondIncidenceMember :
      secondIncidence ∈
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).zipIdx)
    {firstOrigin secondOrigin : RawSegmentOrigin}
    (firstOriginMember :
      firstOrigin ∈ rawSegmentOrigins source sourcePlacement
        presentation.routes firstIncidence.1.clauseIndex
        firstIncidence.1.literalIndex)
    (secondOriginMember :
      secondOrigin ∈ rawSegmentOrigins source sourcePlacement
        presentation.routes secondIncidence.1.clauseIndex
        secondIncidence.1.literalIndex)
    (originalEq : firstOrigin.original = secondOrigin.original) :
    firstOrigin.sourceClauseIndex = secondOrigin.sourceClauseIndex ∧
      firstOrigin.sourceLiteralIndex = secondOrigin.sourceLiteralIndex := by
  rcases rawSegmentOrigin_exists_source_origin presentation
      firstIncidenceMember firstOriginMember with
    ⟨firstClause, firstLiteral, firstClauseIndex, firstLiteralIndex,
      firstClauseMember, firstLiteralMember, firstSourceOrigin,
      firstSourceOriginMember, firstOriginalEq,
      firstSourceClauseIndexEq, firstSourceLiteralIndexEq⟩
  rcases rawSegmentOrigin_exists_source_origin presentation
      secondIncidenceMember secondOriginMember with
    ⟨secondClause, secondLiteral, secondClauseIndex, secondLiteralIndex,
      secondClauseMember, secondLiteralMember, secondSourceOrigin,
      secondSourceOriginMember, secondOriginalEq,
      secondSourceClauseIndexEq, secondSourceLiteralIndexEq⟩
  have sourceOriginalEq :
      firstSourceOrigin.original = secondSourceOrigin.original := by
    rw [← firstOriginalEq, ← secondOriginalEq, originalEq]
  have firstSourceFields :=
    sourceSegmentOrigin_source_fields firstSourceOriginMember
  have secondSourceFields :=
    sourceSegmentOrigin_source_fields secondSourceOriginMember
  have sourceRouteIndexEq :
      refinedIncidenceIndex source sourcePlacement firstClause
          firstClauseIndex firstLiteralIndex firstLiteral =
        refinedIncidenceIndex source sourcePlacement secondClause
          secondClauseIndex secondLiteralIndex secondLiteral := by
    rw [← firstSourceFields.1, ← secondSourceFields.1,
      sourceOriginalEq]
  have firstTaggedMember := refinedIncidenceIndex_tagged_mem
    firstClauseMember firstLiteralMember
  have secondTaggedMember := refinedIncidenceIndex_tagged_mem
    secondClauseMember secondLiteralMember
  have taggedEq := PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
    firstTaggedMember secondTaggedMember sourceRouteIndexEq
  have incidenceEq := congrArg Prod.fst taggedEq
  have sourceClauseIndexEq : firstClauseIndex = secondClauseIndex :=
    congrArg CNFIncidence.clauseIndex incidenceEq
  have sourceLiteralIndexEq : firstLiteralIndex = secondLiteralIndex :=
    congrArg CNFIncidence.literalIndex incidenceEq
  constructor
  · exact firstSourceClauseIndexEq.trans
      (sourceClauseIndexEq.trans secondSourceClauseIndexEq.symm)
  · exact firstSourceLiteralIndexEq.trans
      (sourceLiteralIndexEq.trans secondSourceLiteralIndexEq.symm)

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
