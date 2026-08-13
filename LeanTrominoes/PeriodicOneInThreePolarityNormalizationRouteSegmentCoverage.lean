/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSegmentOrigins

/-!
# Global segment coverage for polarity-normalized route splitting

The local provenance lists are assembled in the same clause-major,
literal-minor order as the raw normalized incidence drawing.  Forgetting the
provenance component then recovers the drawing's complete indexed segment
list.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Continuously planar refined source drawing from which raw routes are
split. -/
def refinedIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement)
    (refinedRouteFamily presentation).routes

/-- Raw normalized incidence drawing before the fresh-variable gauge. -/
def rawIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) : PeriodicGridDrawing :=
  PositionedPeriodicCNF.incidenceDrawing
    (rawFormula source sourcePlacement presentation.routes)
    (rawPlacement sourcePlacement presentation.routes)
    (rawIncidenceRoutes source sourcePlacement presentation.routes)

/-- The `idxOf` route tag stored in source provenance is the genuine tag of
the selected refined-source incidence. -/
theorem refinedIncidenceIndex_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx) :
    (CNFIncidence.mk sourceClauseIndex sourceClause.literals
        sourceLiteralIndex sourceLiteral,
      refinedIncidenceIndex source sourcePlacement sourceClause
        sourceClauseIndex sourceLiteralIndex sourceLiteral) ∈
      (PeriodicCNF.incidencesWithMetadata
        (refinedSource source sourcePlacement).erase).zipIdx := by
  rcases PositionedPeriodicCNF.exists_taggedIncidence_of_members
      (refinedSource source sourcePlacement)
      sourceClauseMember sourceLiteralMember with
    ⟨_incidenceIndex, taggedMember⟩
  have incidenceMember := List.fst_mem_of_mem_zipIdx taggedMember
  rw [List.mem_zipIdx_iff_getElem?]
  exact List.getElem?_idxOf incidenceMember

/-- Every unretagged source-origin entry denotes a genuine indexed segment of
the refined incidence drawing. -/
theorem sourceSegmentOrigin_original_mem
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
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    {origin : RawSegmentOrigin}
    (originMember :
      origin ∈ sourceSegmentOrigins
        (refinedIncidenceIndex source sourcePlacement sourceClause
          sourceClauseIndex sourceLiteralIndex sourceLiteral)
        sourceClauseIndex sourceLiteralIndex
        (refinedRoute presentation.routes sourceClauseIndex
          sourceLiteralIndex)) :
    origin.original ∈
      (refinedIncidenceDrawing presentation).indexedSegments := by
  rcases List.mem_map.mp originMember with
    ⟨taggedSegment, taggedSegmentMember, originEq⟩
  subst origin
  have taggedIncidenceMember := refinedIncidenceIndex_tagged_mem
    sourceClauseMember sourceLiteralMember
  have taggedRouteMember :
      (refinedRoute presentation.routes sourceClauseIndex sourceLiteralIndex,
        refinedIncidenceIndex source sourcePlacement sourceClause
          sourceClauseIndex sourceLiteralIndex sourceLiteral) ∈
        (refinedIncidenceDrawing presentation).edgeRoutes.zipIdx := by
    unfold refinedIncidenceDrawing PositionedPeriodicCNF.incidenceDrawing
    rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
      List.zipIdx_map]
    exact List.mem_map.mpr ⟨_, taggedIncidenceMember, by
      simp [refinedRouteFamily_routes]⟩
  unfold refinedIncidenceDrawing PeriodicGridDrawing.indexedSegments
  exact List.mem_flatMap.mpr ⟨_, taggedRouteMember,
    List.mem_map.mpr ⟨taggedSegment, taggedSegmentMember, rfl⟩⟩

/-- Retagging cannot introduce a new original source occurrence. -/
theorem original_mem_of_mem_retagOrigins
    {origin : RawSegmentOrigin}
    {origins : List RawSegmentOrigin}
    {outputClauseIndex outputLiteralIndex : Nat}
    {fragment : RawRouteFragment}
    {latticeShift : Cell} {reversed : Bool}
    (originMember :
      origin ∈ retagOrigins outputClauseIndex outputLiteralIndex fragment
        latticeShift reversed origins) :
    origin.original ∈ origins.map RawSegmentOrigin.original := by
  have mappedMember : origin.original ∈
      (retagOrigins outputClauseIndex outputLiteralIndex fragment
        latticeShift reversed origins).map RawSegmentOrigin.original :=
    List.mem_map_of_mem originMember
  rwa [retagOrigins_map_original] at mappedMember

/-- Membership of an original occurrence in the unretagged source table is
enough to recover membership in the refined drawing. -/
theorem sourceOriginal_mem_of_mem_sourceSegmentOrigins_map
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
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    {original : IndexedGridSegment}
    (originalMember :
      original ∈
        (sourceSegmentOrigins
          (refinedIncidenceIndex source sourcePlacement sourceClause
            sourceClauseIndex sourceLiteralIndex sourceLiteral)
          sourceClauseIndex sourceLiteralIndex
          (refinedRoute presentation.routes sourceClauseIndex
            sourceLiteralIndex)).map RawSegmentOrigin.original) :
    original ∈
      (refinedIncidenceDrawing presentation).indexedSegments := by
  rcases List.mem_map.mp originalMember with
    ⟨origin, originMember, originalEq⟩
  rw [← originalEq]
  exact sourceSegmentOrigin_original_mem presentation
    sourceClauseMember sourceLiteralMember originMember

/-- Every provenance entry selected by a genuine raw incidence points to a
genuine indexed segment of the refined source drawing. -/
theorem rawSegmentOrigin_original_mem
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
    origin.original ∈
      (refinedIncidenceDrawing presentation).indexedSegments := by
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
  have finish (originalInBase : origin.original ∈
      base.map RawSegmentOrigin.original) :
      origin.original ∈
        (refinedIncidenceDrawing presentation).indexedSegments := by
    exact sourceOriginal_mem_of_mem_sourceSegmentOrigins_map presentation
      sourceClauseMember sourceLiteralMember originalInBase
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
      exact finish (original_mem_of_mem_retagOrigins originMember)
    · simp only [rawSegmentOriginsForMetadata, originEq,
          sourceLiteralLookup, compatible] at originMember
      apply finish
      have selected : origin.original ∈
          (base.map RawSegmentOrigin.original).take 1 := by
        simpa [base, List.map_take] using
          (original_mem_of_mem_retagOrigins originMember)
      exact List.mem_of_mem_take selected
  · rcases complement with ⟨originEq, outputIndexCases⟩
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq, if_pos]
          at originMember
      apply finish
      have selected : origin.original ∈
          ((base.map RawSegmentOrigin.original).drop 1).take 1 := by
        simpa [base, List.map_take, List.map_drop] using
          (original_mem_of_mem_retagOrigins originMember)
      have inDrop : origin.original ∈
          (base.map RawSegmentOrigin.original).drop 1 :=
        List.mem_of_mem_take selected
      exact List.mem_of_mem_drop inDrop
    · rw [outputIndexEq] at originMember
      simp only [rawSegmentOriginsForMetadata, originEq,
        if_neg (by omega : (1 : Nat) ≠ 0), if_true] at originMember
      apply finish
      have selected : origin.original ∈
          (base.map RawSegmentOrigin.original).drop 2 := by
        simpa [base, List.map_drop] using
          (original_mem_of_mem_retagOrigins originMember)
      exact List.mem_of_mem_drop selected

/-- Every raw indexed segment paired with its refined-source provenance, in
the raw drawing's exact route and segment order. -/
def rawIndexedSegmentOrigins
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    List (IndexedGridSegment × RawSegmentOrigin) :=
  (PeriodicCNF.incidencesWithMetadata
      (rawFormula source sourcePlacement presentation.routes).erase).zipIdx.flatMap
    fun taggedIncidence =>
      (rawSegmentOrigins source sourcePlacement presentation.routes
        taggedIncidence.1.clauseIndex
        taggedIncidence.1.literalIndex).zipIdx.map fun taggedOrigin =>
          (⟨taggedIncidence.2, taggedOrigin.2,
              taggedOrigin.1.realize
                (refinedIncidenceDrawing presentation)⟩,
            taggedOrigin.1)

/-- Forgetting provenance recovers exactly the raw drawing's indexed segment
list. -/
theorem rawIndexedSegmentOrigins_map_fst
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    (rawIndexedSegmentOrigins presentation).map Prod.fst =
      (rawIncidenceDrawing presentation).indexedSegments := by
  have routesEq :
      (rawIncidenceDrawing presentation).edgeRoutes =
        (PeriodicCNF.incidencesWithMetadata
          (rawFormula source sourcePlacement presentation.routes).erase).map
            (fun incidence =>
              rawIncidenceRoutes source sourcePlacement presentation.routes
                incidence.clauseIndex incidence.literalIndex) := by
    exact PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map
      (rawFormula source sourcePlacement presentation.routes)
      (rawIncidenceRoutes source sourcePlacement presentation.routes)
  unfold rawIndexedSegmentOrigins PeriodicGridDrawing.indexedSegments
  rw [routesEq, List.zipIdx_map]
  simp only [List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro taggedIncidence taggedIncidenceMember
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  have segments := rawSegmentOrigins_realize_of_output_members
    presentation outputClauseMember outputLiteralMember
  simp only [Prod.map, id_eq] at segments ⊢
  unfold refinedIncidenceDrawing
  rw [← segments, List.zipIdx_map]
  simp [List.map_map, Function.comp_def]

/-- Every indexed segment in the raw drawing has a provenance occurrence at
the same route and within-route indices. -/
theorem rawIndexedSegment_has_origin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {indexed : IndexedGridSegment}
    (indexedMember :
      indexed ∈ (rawIncidenceDrawing presentation).indexedSegments) :
    ∃ taggedIncidence : CNFIncidence (PolarityNormalizedVariable Variable) × Nat,
      ∃ taggedOrigin : RawSegmentOrigin × Nat,
        taggedIncidence ∈
          (PeriodicCNF.incidencesWithMetadata
            (rawFormula source sourcePlacement presentation.routes).erase).zipIdx ∧
        taggedOrigin ∈
          (rawSegmentOrigins source sourcePlacement presentation.routes
            taggedIncidence.1.clauseIndex
            taggedIncidence.1.literalIndex).zipIdx ∧
        indexed =
          ⟨taggedIncidence.2, taggedOrigin.2,
            taggedOrigin.1.realize
              (refinedIncidenceDrawing presentation)⟩ := by
  have provenanceMember :
      indexed ∈ (rawIndexedSegmentOrigins presentation).map Prod.fst := by
    rw [rawIndexedSegmentOrigins_map_fst]
    exact indexedMember
  rcases List.mem_map.mp provenanceMember with
    ⟨pair, pairMember, pairValueEq⟩
  unfold rawIndexedSegmentOrigins at pairMember
  rcases List.mem_flatMap.mp pairMember with
    ⟨taggedIncidence, taggedIncidenceMember, pairMember⟩
  rcases List.mem_map.mp pairMember with
    ⟨taggedOrigin, taggedOriginMember, pairEq⟩
  subst pair
  exact ⟨taggedIncidence, taggedOrigin,
    taggedIncidenceMember, taggedOriginMember, pairValueEq.symm⟩

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
