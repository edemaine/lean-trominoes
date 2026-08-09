import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRefinedEndpointContacts
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteFragments
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSegmentInjectivity

/-!
# Route-level provenance for polarity normalization

Every genuine raw normalized incidence route is a whole, prefix, reversed
middle, or suffix fragment of one complete refined source route, followed by
a whole-period translation.  This file packages that classification at the
route level and proves that a source-route occurrence together with its
fragment kind uniquely identifies the raw incidence occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

open PeriodicOneInThreePolarityNormalization

/-- Logical case selecting one of the four route fragments. -/
inductive RawRouteShape
    {Variable : Type*}
    (metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable)
    (sourceLiteral : PeriodicLiteral Variable)
    (sourceLiteralIndex outputLiteralIndex : Nat) :
    RawRouteFragment → Cell → Prop where
  | whole
      (metadataOrigin : metadata.origin = .normalized)
      (sourceIndex : sourceLiteralIndex = outputLiteralIndex)
      (compatible : sourceLiteral.value =
        normalizedPolarity sourceLiteralIndex) :
      RawRouteShape metadata sourceLiteral sourceLiteralIndex
        outputLiteralIndex .whole (0, 0)
  | prefix
      (metadataOrigin : metadata.origin = .normalized)
      (sourceIndex : sourceLiteralIndex = outputLiteralIndex)
      (incompatible : sourceLiteral.value ≠
        normalizedPolarity sourceLiteralIndex) :
      RawRouteShape metadata sourceLiteral sourceLiteralIndex
        outputLiteralIndex .prefix (0, 0)
  | middle
      (metadataOrigin : metadata.origin =
        .complement sourceLiteralIndex sourceLiteral)
      (outputIndex : outputLiteralIndex = 0)
      (incompatible : sourceLiteral.value ≠
        normalizedPolarity sourceLiteralIndex) :
      RawRouteShape metadata sourceLiteral sourceLiteralIndex
        outputLiteralIndex .middle
          (complementLatticeShift sourceLiteral)
  | suffix
      (metadataOrigin : metadata.origin =
        .complement sourceLiteralIndex sourceLiteral)
      (outputIndex : outputLiteralIndex = 1)
      (incompatible : sourceLiteral.value ≠
        normalizedPolarity sourceLiteralIndex) :
      RawRouteShape metadata sourceLiteral sourceLiteralIndex
        outputLiteralIndex .suffix
          (complementLatticeShift sourceLiteral)

/-- Eliminate a route shape without dependent elimination on descriptor
projections. -/
theorem RawRouteShape.classify
    {Variable : Type*}
    {metadata :
      PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
        Variable}
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex outputLiteralIndex : Nat}
    {fragment : RawRouteFragment} {latticeShift : Cell}
    (shape : RawRouteShape metadata sourceLiteral sourceLiteralIndex
      outputLiteralIndex fragment latticeShift) :
    (fragment = .whole ∧ metadata.origin = .normalized ∧
        sourceLiteralIndex = outputLiteralIndex ∧
        sourceLiteral.value = normalizedPolarity sourceLiteralIndex) ∨
      (fragment = .prefix ∧ metadata.origin = .normalized ∧
        sourceLiteralIndex = outputLiteralIndex ∧
        sourceLiteral.value ≠ normalizedPolarity sourceLiteralIndex) ∨
      (fragment = .middle ∧ metadata.origin =
          .complement sourceLiteralIndex sourceLiteral ∧
        outputLiteralIndex = 0 ∧
        sourceLiteral.value ≠ normalizedPolarity sourceLiteralIndex) ∨
      (fragment = .suffix ∧ metadata.origin =
          .complement sourceLiteralIndex sourceLiteral ∧
        outputLiteralIndex = 1 ∧
        sourceLiteral.value ≠ normalizedPolarity sourceLiteralIndex) := by
  cases shape with
  | whole origin index compatible =>
      exact Or.inl ⟨rfl, origin, index, compatible⟩
  | «prefix» origin index incompatible =>
      exact Or.inr (Or.inl ⟨rfl, origin, index, incompatible⟩)
  | middle origin index incompatible =>
      exact Or.inr (Or.inr (Or.inl
        ⟨rfl, origin, index, incompatible⟩))
  | suffix origin index incompatible =>
      exact Or.inr (Or.inr (Or.inr
        ⟨rfl, origin, index, incompatible⟩))

/-- Complete route-level provenance for one genuine raw incidence. -/
structure RawRouteDescriptor
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat) where
  metadata :
    PeriodicOneInThreePolarityNormalizationPositioned.ClauseMetadata
      Variable
  sourceLiteral : PeriodicLiteral Variable
  sourceLiteralIndex : Nat
  metadataLookup :
    (clauseMetadata source sourcePlacement presentation.routes)[
        taggedIncidence.1.clauseIndex]? = some metadata
  sourceClauseMember :
    (metadata.sourceClause, metadata.sourceClauseIndex) ∈
      (refinedSource source sourcePlacement).clauses.zipIdx
  sourceLiteralMember :
    (sourceLiteral, sourceLiteralIndex) ∈
      metadata.sourceClause.literals.zipIdx
  fragment : RawRouteFragment
  latticeShift : Cell
  shape :
    RawRouteShape metadata sourceLiteral sourceLiteralIndex
      taggedIncidence.1.literalIndex fragment latticeShift
  routeEq :
    rawIncidenceRoutes source sourcePlacement presentation.routes
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex =
      PeriodicOrthocrossing.translatePolyline
        ((refinedIncidenceDrawing presentation).periodTranslation
          latticeShift)
        (fragment.select
          (refinedRoute presentation.routes metadata.sourceClauseIndex
            sourceLiteralIndex))

namespace RawRouteDescriptor

/-- Metadata-rich source incidence selected by a raw route descriptor. -/
def sourceIncidence
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    CNFIncidence Variable :=
  CNFIncidence.mk descriptor.metadata.sourceClauseIndex
    descriptor.metadata.sourceClause.literals
    descriptor.sourceLiteralIndex descriptor.sourceLiteral

/-- Flat index of the complete refined source route. -/
def sourceRouteIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence) : Nat :=
  refinedIncidenceIndex source sourcePlacement descriptor.metadata.sourceClause
    descriptor.metadata.sourceClauseIndex descriptor.sourceLiteralIndex
    descriptor.sourceLiteral

/-- The descriptor's source incidence occurs at its declared refined flat
route index. -/
theorem sourceTaggedIncidenceMember
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    (descriptor.sourceIncidence, descriptor.sourceRouteIndex) ∈
      (PeriodicCNF.incidencesWithMetadata
        (refinedSource source sourcePlacement).erase).zipIdx := by
  exact refinedIncidenceIndex_tagged_mem
    descriptor.sourceClauseMember descriptor.sourceLiteralMember

/-- The descriptor's complete source route occurs at the same refined flat
route index. -/
theorem sourceTaggedRouteMember
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    (refinedRoute presentation.routes descriptor.metadata.sourceClauseIndex
        descriptor.sourceLiteralIndex,
      descriptor.sourceRouteIndex) ∈
        (refinedIncidenceDrawing presentation).edgeRoutes.zipIdx := by
  have member := PositionedPeriodicCNF.taggedRoute_mem_of_taggedIncidence
    (refinedSource source sourcePlacement)
    (refinedPlacement sourcePlacement)
    (refinedRouteFamily presentation).routes
    descriptor.sourceTaggedIncidenceMember
  simpa [refinedIncidenceDrawing, refinedRouteFamily_routes,
    sourceIncidence] using member

/-- Every descriptor's complete source route contains the three reserved
segments needed by route splitting. -/
theorem sourceRoute_length_ge_four
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement}
    {taggedIncidence :
      CNFIncidence (PolarityNormalizedVariable Variable) × Nat}
    (descriptor : RawRouteDescriptor presentation taggedIncidence) :
    4 ≤ (refinedRoute presentation.routes
      descriptor.metadata.sourceClauseIndex
      descriptor.sourceLiteralIndex).length :=
  refinedRoute_length_ge_four_of_members presentation
    descriptor.sourceClauseMember descriptor.sourceLiteralMember

end RawRouteDescriptor

/-- Every genuine raw incidence admits a complete route descriptor. -/
theorem exists_rawRouteDescriptor
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
    Nonempty (RawRouteDescriptor presentation taggedIncidence) := by
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (rawFormula source sourcePlacement presentation.routes)
      taggedIncidenceMember with
    ⟨outputClause, outputLiteral, outputClauseMember,
      outputLiteralMember, _incidenceEq⟩
  rcases exists_raw_source_of_output_members presentation
      outputClauseMember outputLiteralMember with
    ⟨metadata, sourceLiteral, sourceLiteralIndex, metadataLookup,
      sourceClauseMember, sourceLiteralMember, normalized | complement⟩
  · rcases normalized with ⟨originEq, sourceIndexEq⟩
    have sourceLiteralLookup :=
      (List.mem_zipIdx_iff_getElem?).mp sourceLiteralMember
    have outputLiteralLookup :
        metadata.sourceClause.literals[taggedIncidence.1.literalIndex]? =
          some sourceLiteral := by
      simpa [sourceIndexEq] using sourceLiteralLookup
    by_cases compatible : sourceLiteral.value =
        normalizedPolarity sourceLiteralIndex
    · refine ⟨{
        metadata := metadata
        sourceLiteral := sourceLiteral
        sourceLiteralIndex := sourceLiteralIndex
        metadataLookup := metadataLookup
        sourceClauseMember := sourceClauseMember
        sourceLiteralMember := sourceLiteralMember
        fragment := .whole
        latticeShift := (0, 0)
        shape := RawRouteShape.whole originEq sourceIndexEq compatible
        routeEq := ?_ }⟩
      rw [rawIncidenceRoutes_of_metadata_lookup
        source sourcePlacement presentation.routes metadata
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
        metadataLookup]
      rw [rawRouteForMetadata_normalized_compatible
        sourcePlacement presentation.routes metadata sourceLiteral
        taggedIncidence.1.literalIndex originEq outputLiteralLookup]
      · rw [sourceIndexEq]
        change refinedRoute presentation.routes metadata.sourceClauseIndex
            taggedIncidence.1.literalIndex =
          PeriodicOrthocrossing.translatePolyline (0, 0)
            (refinedRoute presentation.routes metadata.sourceClauseIndex
              taggedIncidence.1.literalIndex)
        rw [PeriodicOrthocrossing.translatePolyline_zero]
      · simpa [sourceIndexEq] using compatible
    · refine ⟨{
        metadata := metadata
        sourceLiteral := sourceLiteral
        sourceLiteralIndex := sourceLiteralIndex
        metadataLookup := metadataLookup
        sourceClauseMember := sourceClauseMember
        sourceLiteralMember := sourceLiteralMember
        fragment := .prefix
        latticeShift := (0, 0)
        shape := RawRouteShape.prefix originEq sourceIndexEq compatible
        routeEq := ?_ }⟩
      rw [rawIncidenceRoutes_of_metadata_lookup
        source sourcePlacement presentation.routes metadata
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
        metadataLookup]
      rw [rawRouteForMetadata_normalized_incompatible
        sourcePlacement presentation.routes metadata sourceLiteral
        taggedIncidence.1.literalIndex originEq outputLiteralLookup]
      · rw [sourceIndexEq]
        change (refinedRoute presentation.routes metadata.sourceClauseIndex
            taggedIncidence.1.literalIndex).take 2 =
          PeriodicOrthocrossing.translatePolyline (0, 0)
            ((refinedRoute presentation.routes metadata.sourceClauseIndex
              taggedIncidence.1.literalIndex).take 2)
        rw [PeriodicOrthocrossing.translatePolyline_zero]
      · simpa [sourceIndexEq] using compatible
  · rcases complement with ⟨originEq, outputIndexCases⟩
    have metadataMember : metadata ∈
        clauseMetadata source sourcePlacement presentation.routes := by
      rcases List.getElem?_eq_some_iff.mp metadataLookup with
        ⟨metadataIndexLt, metadataAt⟩
      rw [← metadataAt]
      exact List.getElem_mem metadataIndexLt
    have incompatible : sourceLiteral.value ≠
        normalizedPolarity sourceLiteralIndex :=
      (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata_complement_valid
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement)
        (by simpa only [clauseMetadata] using metadataMember)
        originEq).2.2
    rcases outputIndexCases with outputIndexEq | outputIndexEq
    · refine ⟨{
        metadata := metadata
        sourceLiteral := sourceLiteral
        sourceLiteralIndex := sourceLiteralIndex
        metadataLookup := metadataLookup
        sourceClauseMember := sourceClauseMember
        sourceLiteralMember := sourceLiteralMember
        fragment := .middle
        latticeShift := complementLatticeShift sourceLiteral
        shape := RawRouteShape.middle originEq outputIndexEq incompatible
        routeEq := ?_ }⟩
      rw [rawIncidenceRoutes_of_metadata_lookup
        source sourcePlacement presentation.routes metadata
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
        metadataLookup]
      rw [outputIndexEq,
        rawRouteForMetadata_complement_fresh
          sourcePlacement presentation.routes metadata sourceLiteral
          sourceLiteralIndex originEq,
        complementCanonicalShift_eq_periodTranslation presentation]
      rfl
    · refine ⟨{
        metadata := metadata
        sourceLiteral := sourceLiteral
        sourceLiteralIndex := sourceLiteralIndex
        metadataLookup := metadataLookup
        sourceClauseMember := sourceClauseMember
        sourceLiteralMember := sourceLiteralMember
        fragment := .suffix
        latticeShift := complementLatticeShift sourceLiteral
        shape := RawRouteShape.suffix originEq outputIndexEq incompatible
        routeEq := ?_ }⟩
      rw [rawIncidenceRoutes_of_metadata_lookup
        source sourcePlacement presentation.routes metadata
        taggedIncidence.1.clauseIndex taggedIncidence.1.literalIndex
        metadataLookup]
      rw [outputIndexEq,
        rawRouteForMetadata_complement_original
          sourcePlacement presentation.routes metadata sourceLiteral
          sourceLiteralIndex originEq,
        complementCanonicalShift_eq_periodTranslation presentation]
      rfl

/-- Equal source-route indices and equal fragment kinds identify the same
raw incidence occurrence. -/
theorem taggedIncidence_eq_of_descriptors_sourceRouteIndex_fragment_eq
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
    (first : RawRouteDescriptor presentation firstIncidence)
    (second : RawRouteDescriptor presentation secondIncidence)
    (sourceRouteIndexEq :
      first.sourceRouteIndex = second.sourceRouteIndex)
    (fragmentEq : first.fragment = second.fragment) :
    firstIncidence = secondIncidence := by
  have sourceTaggedEq :=
    PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_snd_eq'
      first.sourceTaggedIncidenceMember
      second.sourceTaggedIncidenceMember sourceRouteIndexEq
  have sourceIncidenceEq :
      first.sourceIncidence = second.sourceIncidence :=
    congrArg Prod.fst sourceTaggedEq
  have sourceClauseIndexEq :
      first.metadata.sourceClauseIndex =
        second.metadata.sourceClauseIndex :=
    congrArg CNFIncidence.clauseIndex sourceIncidenceEq
  have sourceLiteralIndexEq :
      first.sourceLiteralIndex = second.sourceLiteralIndex :=
    congrArg CNFIncidence.literalIndex sourceIncidenceEq
  have sourceLiteralEq :
      first.sourceLiteral = second.sourceLiteral :=
    congrArg CNFIncidence.literal sourceIncidenceEq
  have finish
      (metadataKeysEq : clauseMetadataKey first.metadata =
        clauseMetadataKey second.metadata)
      (outputLiteralIndexEq :
        firstIncidence.1.literalIndex =
          secondIncidence.1.literalIndex) :
      firstIncidence = secondIncidence := by
    have firstBaseLookup :
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement))[
            firstIncidence.1.clauseIndex]? = some first.metadata := by
      simpa only [clauseMetadata] using first.metadataLookup
    have secondBaseLookup :
        (PeriodicOneInThreePolarityNormalizationPositioned.formulaClauseMetadata
          (rawPositions sourcePlacement presentation.routes)
          (refinedSource source sourcePlacement))[
            secondIncidence.1.clauseIndex]? = some second.metadata := by
      simpa only [clauseMetadata] using second.metadataLookup
    have outputClauseIndexEq :
        firstIncidence.1.clauseIndex = secondIncidence.1.clauseIndex :=
      formulaClauseMetadata_lookup_key_injective
        (rawPositions sourcePlacement presentation.routes)
        (refinedSource source sourcePlacement)
        firstBaseLookup secondBaseLookup metadataKeysEq
    have incidenceEq : firstIncidence.1 = secondIncidence.1 :=
      PeriodicCNF.incidence_eq_of_indices_eq
        (rawFormula source sourcePlacement presentation.routes).erase
        (List.fst_mem_of_mem_zipIdx firstIncidenceMember)
        (List.fst_mem_of_mem_zipIdx secondIncidenceMember)
        outputClauseIndexEq outputLiteralIndexEq
    exact
      PeriodicThreeDM.tagged_eq_of_mem_zipIdx_of_fst_eq_of_nodup
        (PeriodicCNF.incidencesWithMetadata_nodup
          (rawFormula source sourcePlacement presentation.routes).erase)
        firstIncidenceMember secondIncidenceMember incidenceEq
  rcases first.shape.classify with firstWhole | firstPrefix |
      firstMiddle | firstSuffix
  · rcases firstWhole with
      ⟨firstFragment, firstOrigin, firstSourceIndex, firstCompatible⟩
    rcases second.shape.classify with secondWhole | secondPrefix |
        secondMiddle | secondSuffix
    · rcases secondWhole with
        ⟨secondFragment, secondOrigin, secondSourceIndex, _⟩
      apply finish
      · simp [clauseMetadataKey, firstOrigin, secondOrigin,
          sourceClauseIndexEq]
      · exact firstSourceIndex.symm.trans
          (sourceLiteralIndexEq.trans secondSourceIndex)
    · exact (secondPrefix.2.2.2
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          firstCompatible)).elim
    · exact (secondMiddle.2.2.2
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          firstCompatible)).elim
    · exact (secondSuffix.2.2.2
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          firstCompatible)).elim
  · rcases firstPrefix with
      ⟨firstFragment, firstOrigin, firstSourceIndex, firstIncompatible⟩
    rcases second.shape.classify with secondWhole | secondPrefix |
        secondMiddle | secondSuffix
    · exact (firstIncompatible
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          secondWhole.2.2.2)).elim
    · rcases secondPrefix with
        ⟨secondFragment, secondOrigin, secondSourceIndex, _⟩
      apply finish
      · simp [clauseMetadataKey, firstOrigin, secondOrigin,
          sourceClauseIndexEq]
      · exact firstSourceIndex.symm.trans
          (sourceLiteralIndexEq.trans secondSourceIndex)
    · simp [firstFragment, secondMiddle.1] at fragmentEq
    · simp [firstFragment, secondSuffix.1] at fragmentEq
  · rcases firstMiddle with
      ⟨firstFragment, firstOrigin, firstOutputIndex, firstIncompatible⟩
    rcases second.shape.classify with secondWhole | secondPrefix |
        secondMiddle | secondSuffix
    · exact (firstIncompatible
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          secondWhole.2.2.2)).elim
    · simp [firstFragment, secondPrefix.1] at fragmentEq
    · rcases secondMiddle with
        ⟨secondFragment, secondOrigin, secondOutputIndex, _⟩
      apply finish
      · simp [clauseMetadataKey, firstOrigin, secondOrigin,
          sourceClauseIndexEq, sourceLiteralIndexEq, sourceLiteralEq]
      · exact firstOutputIndex.trans secondOutputIndex.symm
    · simp [firstFragment, secondSuffix.1] at fragmentEq
  · rcases firstSuffix with
      ⟨firstFragment, firstOrigin, firstOutputIndex, firstIncompatible⟩
    rcases second.shape.classify with secondWhole | secondPrefix |
        secondMiddle | secondSuffix
    · exact (firstIncompatible
        (by simpa [sourceLiteralEq, sourceLiteralIndexEq] using
          secondWhole.2.2.2)).elim
    · simp [firstFragment, secondPrefix.1] at fragmentEq
    · simp [firstFragment, secondMiddle.1] at fragmentEq
    · rcases secondSuffix with
        ⟨secondFragment, secondOrigin, secondOutputIndex, _⟩
      apply finish
      · simp [clauseMetadataKey, firstOrigin, secondOrigin,
          sourceClauseIndexEq, sourceLiteralIndexEq, sourceLiteralEq]
      · exact firstOutputIndex.trans secondOutputIndex.symm

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
