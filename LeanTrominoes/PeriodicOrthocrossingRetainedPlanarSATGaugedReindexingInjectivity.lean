import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedSourceOrbitMembership

/-!
# Occurrence identity under retained source reindexing

Source reindexing may select a different retained metadata entry, but it
preserves the anchor-normalized clause orbit and translates the
pre-normalization anchor predictably.  Consequently, if a reindexed
occurrence and a second occurrence select the same finite incidence and
within-route segment index, their original periodic segment-occurrence keys
were already equal.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Transport a finite representative across equality of its phantom common
shift parameter. -/
private def castCommonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift sourceCommonShift targetCommonShift : Cell}
    (equal : sourceCommonShift = targetCommonShift)
    (representative :
      FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift sourceCommonShift) :
    FinalGaugedSegmentCommonShiftRepresentative
      formula indexed shift targetCommonShift :=
  equal ▸ representative

@[simp]
private theorem
    castCommonShiftRepresentative_physicalIncidenceIndex
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift sourceCommonShift targetCommonShift : Cell}
    (equal : sourceCommonShift = targetCommonShift)
    (representative :
      FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift sourceCommonShift) :
    (castCommonShiftRepresentative
        equal representative).physicalIncidenceIndex =
      representative.physicalIncidenceIndex := by
  cases equal
  rfl

/-- A physical source reindexing cannot collapse two distinct periodic
segment occurrences. -/
theorem
    FinalGaugedSegmentMetadataReindexing.segmentOccurrenceKey_eq_of_targetPhysicalIncidence_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift reindexShift : Cell}
    {first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing
        first reindexShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexShiftEq :
      reindexShift =
        Cell.sub first.physicalShift second.physicalShift)
    (sourceClauseNonempty :
      first.routeWitness.metadata.clause.literals ≠ [])
    (targetPhysicalIncidenceEq :
      metadataPhysicalIncidence
          reindexing.targetMetadata
          reindexing.targetMetadataIndex
          reindexing.targetLiteral first.taggedLiteral.2 =
        metadataPhysicalIncidence
          second.routeWitness.metadata
          second.routeWitness.metadataIndex
          second.routeWitness.literal second.taggedLiteral.2)
    (segmentIndexEq :
      firstIndexed.segmentIndex =
        secondIndexed.segmentIndex) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        firstIndexed firstShift =
      PeriodicGridDrawing.SegmentOccurrenceKey
        secondIndexed secondShift := by
  have targetMetadataIndexEq :
      reindexing.targetMetadataIndex =
        second.routeWitness.metadataIndex :=
    congrArg EmbeddedCNFIncidence.clauseIndex
      targetPhysicalIncidenceEq
  have targetMetadataEq :
      reindexing.targetMetadata =
        second.routeWitness.metadata := by
    have targetLookup := reindexing.targetMetadataLookup
    have secondLookup := second.routeWitness.metadataLookup
    rw [targetMetadataIndexEq] at targetLookup
    exact Option.some.inj
      (targetLookup.symm.trans secondLookup)
  have literalIndexEq :
      first.taggedLiteral.2 =
        second.taggedLiteral.2 :=
    congrArg EmbeddedCNFIncidence.literalIndex
      targetPhysicalIncidenceEq
  have finalLiteralsEq :
      first.routeWitness.finalClause.literals =
        second.routeWitness.finalClause.literals := by
    calc
      first.routeWitness.finalClause.literals =
          metadataGaugedNormalizedClause
            formula first.routeWitness.metadata :=
        first.routeWitness.normalizedLiteralsEq.symm
      _ =
          metadataGaugedNormalizedClause
            formula reindexing.targetMetadata :=
        reindexing.target_normalizedClause_eq.symm
      _ =
          metadataGaugedNormalizedClause
            formula second.routeWitness.metadata := by
        rw [targetMetadataEq]
      _ = second.routeWitness.finalClause.literals :=
        second.routeWitness.normalizedLiteralsEq
  let source :=
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  have firstFinalClauseMember :
      first.routeWitness.finalClause ∈
        source.deduplicateByLiterals.clauses := by
    apply List.mem_iff_getElem?.mpr
    exact
      ⟨first.taggedClause.2,
        by
          simpa only [source,
            retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
            using first.routeWitness.finalClauseLookup⟩
  have secondFinalClauseMember :
      second.routeWitness.finalClause ∈
        source.deduplicateByLiterals.clauses := by
    apply List.mem_iff_getElem?.mpr
    exact
      ⟨second.taggedClause.2,
        by
          simpa only [source,
            retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
            using second.routeWitness.finalClauseLookup⟩
  have firstRepresentative :=
    PositionedPeriodicCNF.eq_representative_of_mem_deduplicateByLiterals
      source first.routeWitness.finalClause firstFinalClauseMember
  have secondRepresentative :=
    PositionedPeriodicCNF.eq_representative_of_mem_deduplicateByLiterals
      source second.routeWitness.finalClause secondFinalClauseMember
  have finalClauseEq :
      first.routeWitness.finalClause =
        second.routeWitness.finalClause := by
    calc
      first.routeWitness.finalClause =
          ⟨source.representativeClausePosition
              first.routeWitness.finalClause.literals,
            first.routeWitness.finalClause.literals⟩ :=
        firstRepresentative
      _ =
          ⟨source.representativeClausePosition
              second.routeWitness.finalClause.literals,
            second.routeWitness.finalClause.literals⟩ := by
        rw [finalLiteralsEq]
      _ = second.routeWitness.finalClause :=
        secondRepresentative.symm
  have firstFinalClauseLookup :
      source.deduplicateByLiterals.clauses[
          first.taggedClause.2]? =
        some second.routeWitness.finalClause := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using
        first.routeWitness.finalClauseLookup.trans
          (congrArg some finalClauseEq)
  have secondFinalClauseLookup :
      source.deduplicateByLiterals.clauses[
          second.taggedClause.2]? =
        some second.routeWitness.finalClause := by
    simpa only [source,
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula]
      using second.routeWitness.finalClauseLookup
  have clauseIndexEq :
      first.taggedClause.2 = second.taggedClause.2 :=
    List.Nodup.index_eq_of_getElem?_eq_some
      (PositionedPeriodicCNF.deduplicateByLiterals_clauses_nodup
        source)
      firstFinalClauseLookup secondFinalClauseLookup
  have finalClauseCoordinateEq :
      first.finalIncidence.1.clauseIndex =
        second.finalIncidence.1.clauseIndex :=
    first.taggedClauseIndexEq.symm.trans
      (clauseIndexEq.trans second.taggedClauseIndexEq)
  have finalLiteralCoordinateEq :
      first.finalIncidence.1.literalIndex =
        second.finalIncidence.1.literalIndex :=
    first.taggedLiteralIndexEq.symm.trans
      (literalIndexEq.trans
        second.taggedLiteralIndexEq)
  have finalIncidenceEq :
      first.finalIncidence.1 = second.finalIncidence.1 := by
    apply PeriodicCNF.incidence_eq_of_indices_eq
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
    · exact List.fst_mem_of_mem_zipIdx
        first.finalIncidenceMember
    · exact List.fst_mem_of_mem_zipIdx
        second.finalIncidenceMember
    · exact finalClauseCoordinateEq
    · exact finalLiteralCoordinateEq
  have firstFinalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      first.finalIncidenceMember
  have secondFinalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      second.finalIncidenceMember
  have firstFinalLookup' :
      (finalGaugedIncidences formula)[
          first.finalIncidence.2]? =
        some second.finalIncidence.1 :=
    firstFinalLookup.trans (congrArg some finalIncidenceEq)
  have finalIncidenceIndexEq :
      first.finalIncidence.2 =
        second.finalIncidence.2 :=
    List.Nodup.index_eq_of_getElem?_eq_some
      (by
        simpa only [finalGaugedIncidences] using
          PeriodicCNF.incidencesWithMetadata_nodup
            (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
              formula).erase)
      firstFinalLookup' secondFinalLookup
  have routeIndexEq :
      firstIndexed.routeIndex =
        secondIndexed.routeIndex :=
    first.finalIncidenceIndexEq.symm.trans
      (finalIncidenceIndexEq.trans
        second.finalIncidenceIndexEq)
  have targetAnchorEq :=
    reindexing.target_clauseAnchor_eq sourceClauseNonempty
  rw [targetMetadataEq] at targetAnchorEq
  have finalShiftEq :
      firstShift = secondShift := by
    rcases firstShift with ⟨firstShiftX, firstShiftY⟩
    rcases secondShift with ⟨secondShiftX, secondShiftY⟩
    rcases reindexShift with ⟨reindexX, reindexY⟩
    rcases firstAnchorEq :
        PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula first.routeWitness.metadata).literals with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases secondAnchorEq :
        PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause
            formula second.routeWitness.metadata).literals with
      ⟨secondAnchorX, secondAnchorY⟩
    simp only [
      FinalGaugedSegmentOccurrenceWitness.physicalShift,
      firstAnchorEq, secondAnchorEq, Cell.sub,
      Prod.mk.injEq] at reindexShiftEq
    simp only [firstAnchorEq, secondAnchorEq,
      Cell.add, Prod.mk.injEq] at targetAnchorEq
    simp only [Prod.mk.injEq]
    constructor <;> omega
  simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
    Prod.mk.injEq]
  exact ⟨routeIndexEq, segmentIndexEq, finalShiftEq⟩

/-- Distinct original periodic occurrence keys remain distinct as finite
incidence/segment indices after reindexing the first occurrence to the
second one's physical shift. -/
theorem
    FinalGaugedSegmentMetadataReindexing.finiteDifferent_of_segmentOccurrenceKey_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first
        (Cell.sub first.physicalShift second.physicalShift))
    (sourceClauseNonempty :
      first.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    reindexing.toCommonShiftRepresentative.physicalIncidenceIndex ≠
          second.physicalIncidenceIndex ∨
      firstIndexed.segmentIndex ≠
          secondIndexed.segmentIndex := by
  by_cases incidenceIndexNe :
      reindexing.targetPhysicalIncidenceIndex ≠
        second.physicalIncidenceIndex
  · left
    simpa only [
      FinalGaugedSegmentMetadataReindexing.toCommonShiftRepresentative_physicalIncidenceIndex]
      using incidenceIndexNe
  · right
    intro segmentIndexEq
    apply different
    have incidenceIndexEq :
        reindexing.targetPhysicalIncidenceIndex =
          second.physicalIncidenceIndex :=
      not_ne_iff.mp incidenceIndexNe
    have targetLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        reindexing.targetPhysicalIncidenceMember
    have secondLookup :=
      (List.mem_zipIdx_iff_getElem?).mp
        second.physicalIncidenceMember
    rw [incidenceIndexEq] at targetLookup
    have targetPhysicalIncidenceEq :
        metadataPhysicalIncidence
            reindexing.targetMetadata
            reindexing.targetMetadataIndex
            reindexing.targetLiteral first.taggedLiteral.2 =
          metadataPhysicalIncidence
            second.routeWitness.metadata
            second.routeWitness.metadataIndex
            second.routeWitness.literal second.taggedLiteral.2 :=
      Option.some.inj
        (targetLookup.symm.trans secondLookup)
    exact
      reindexing.segmentOccurrenceKey_eq_of_targetPhysicalIncidence_eq
        second rfl sourceClauseNonempty
        targetPhysicalIncidenceEq segmentIndexEq

/-- Reindexing a distinct first occurrence to the second occurrence's
physical shift transfers finite retained planarity back to the original
periodic pair. -/
theorem
    FinalGaugedSegmentMetadataReindexing.interiorsDisjoint
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first
        (Cell.sub first.physicalShift second.physicalShift))
    (sourceClauseNonempty :
      first.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have commonShiftEq :
      Cell.sub first.physicalShift
          (Cell.sub first.physicalShift second.physicalShift) =
        second.physicalShift := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp [Cell.sub]
  let firstRepresentative :=
    castCommonShiftRepresentative commonShiftEq
      reindexing.toCommonShiftRepresentative
  exact
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_interiorsDisjoint
      formula wellFormed degree isLocal clausesNonempty
      firstRepresentative
      second.toCommonShiftRepresentative
      (by
        simpa only [firstRepresentative,
          castCommonShiftRepresentative_physicalIncidenceIndex,
          FinalGaugedSegmentOccurrenceWitness.toCommonShiftRepresentative]
          using
            finiteDifferent_of_segmentOccurrenceKey_ne
              second reindexing sourceClauseNonempty different)

/-- Reindexing a distinct first occurrence to the second occurrence's
physical shift transfers finite asymmetric interior avoidance back to the
original periodic pair. -/
theorem
    FinalGaugedSegmentMetadataReindexing.avoidsInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first
        (Cell.sub first.physicalShift second.physicalShift))
    (sourceClauseNonempty :
      first.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  have commonShiftEq :
      Cell.sub first.physicalShift
          (Cell.sub first.physicalShift second.physicalShift) =
        second.physicalShift := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp [Cell.sub]
  let firstRepresentative :=
    castCommonShiftRepresentative commonShiftEq
      reindexing.toCommonShiftRepresentative
  exact
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_avoidsInterior
      formula wellFormed degree isLocal clausesNonempty
      firstRepresentative
      second.toCommonShiftRepresentative
      (by
        simpa only [firstRepresentative,
          castCommonShiftRepresentative_physicalIncidenceIndex,
          FinalGaugedSegmentOccurrenceWitness.toCommonShiftRepresentative]
          using
            finiteDifferent_of_segmentOccurrenceKey_ne
              second reindexing sourceClauseNonempty different)
      point firstContains

/-- Reindexing a distinct first occurrence to the second occurrence's
physical shift also transfers finite endpoint separation back to the
original periodic pair. -/
theorem
    FinalGaugedSegmentMetadataReindexing.endpointsAvoidInterior
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    {first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift}
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (reindexing :
      FinalGaugedSegmentMetadataReindexing first
        (Cell.sub first.physicalShift second.physicalShift))
    (sourceClauseNonempty :
      first.routeWitness.metadata.clause.literals ≠ [])
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).start ∧
      point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).finish := by
  have commonShiftEq :
      Cell.sub first.physicalShift
          (Cell.sub first.physicalShift second.physicalShift) =
        second.physicalShift := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp [Cell.sub]
  let firstRepresentative :=
    castCommonShiftRepresentative commonShiftEq
      reindexing.toCommonShiftRepresentative
  exact
    retainedDeduplicatedGaugedWrappedDrawing_commonShiftRepresentatives_endpointsAvoidInterior
      formula wellFormed degree isLocal clausesNonempty
      firstRepresentative
      second.toCommonShiftRepresentative
      (by
        simpa only [firstRepresentative,
          castCommonShiftRepresentative_physicalIncidenceIndex,
          FinalGaugedSegmentOccurrenceWitness.toCommonShiftRepresentative]
          using
            finiteDifferent_of_segmentOccurrenceKey_ne
              second reindexing sourceClauseNonempty different)
      point firstContains

/-- The uniform retained source-orbit condition is sufficient to transfer
finite retained planarity to a distinct pair of final periodic segment
occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (condition :
      first.routeWitness.metadata.source.RetainedOrbitCondition
        formula
        (Cell.sub first.physicalShift second.physicalShift))
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_retainedTarget_periodTranslate
          formula degree first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          condition with
    ⟨targetSource, targetMember,
      targetComponentEq, targetLocalClauseIndexEq⟩
  rcases first.exists_metadataReindexing_of_targetSource
      targetSource targetMember targetComponentEq
      targetLocalClauseIndexEq with
    ⟨reindexing⟩
  have sourceMetadataMember :
      first.routeWitness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨first.routeWitness.metadataIndex,
        first.routeWitness.metadataLookup⟩
  have sourceClauseMember :
      first.routeWitness.metadata.clause ∈
        retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr
      ⟨first.routeWitness.metadata,
        sourceMetadataMember, rfl⟩
  exact
    FinalGaugedSegmentMetadataReindexing.interiorsDisjoint
      formula wellFormed degree isLocal clausesNonempty
      second reindexing
      (clausesNonempty
        first.routeWitness.metadata.clause sourceClauseMember)
      different

/-- The uniform retained source-orbit condition also transfers asymmetric
interior-versus-closed avoidance to a distinct pair of final periodic
segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (condition :
      first.routeWitness.metadata.source.RetainedOrbitCondition
        formula
        (Cell.sub first.physicalShift second.physicalShift))
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_retainedTarget_periodTranslate
          formula degree first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          condition with
    ⟨targetSource, targetMember,
      targetComponentEq, targetLocalClauseIndexEq⟩
  rcases first.exists_metadataReindexing_of_targetSource
      targetSource targetMember targetComponentEq
      targetLocalClauseIndexEq with
    ⟨reindexing⟩
  have sourceMetadataMember :
      first.routeWitness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨first.routeWitness.metadataIndex,
        first.routeWitness.metadataLookup⟩
  have sourceClauseMember :
      first.routeWitness.metadata.clause ∈
        retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr
      ⟨first.routeWitness.metadata,
        sourceMetadataMember, rfl⟩
  exact
    FinalGaugedSegmentMetadataReindexing.avoidsInterior
      formula wellFormed degree isLocal clausesNonempty
      second reindexing
      (clausesNonempty
        first.routeWitness.metadata.clause sourceClauseMember)
      different point firstContains

/-- The uniform retained source-orbit condition also transfers endpoint
separation to a distinct pair of final periodic segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_endpointsAvoidInterior_of_first_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (condition :
      first.routeWitness.metadata.source.RetainedOrbitCondition
        formula
        (Cell.sub first.physicalShift second.physicalShift))
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).start ∧
      point ≠
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)).finish := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_retainedTarget_periodTranslate
          formula degree first.source_retainedComponentMember
          (Cell.sub first.physicalShift second.physicalShift)
          condition with
    ⟨targetSource, targetMember,
      targetComponentEq, targetLocalClauseIndexEq⟩
  rcases first.exists_metadataReindexing_of_targetSource
      targetSource targetMember targetComponentEq
      targetLocalClauseIndexEq with
    ⟨reindexing⟩
  have sourceMetadataMember :
      first.routeWitness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨first.routeWitness.metadataIndex,
        first.routeWitness.metadataLookup⟩
  have sourceClauseMember :
      first.routeWitness.metadata.clause ∈
        retainedDrawingPlanarSATFormula formula := by
    rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    exact List.mem_map.mpr
      ⟨first.routeWitness.metadata,
        sourceMetadataMember, rfl⟩
  exact
    FinalGaugedSegmentMetadataReindexing.endpointsAvoidInterior
      formula wellFormed degree isLocal clausesNonempty
      second reindexing
      (clausesNonempty
        first.routeWitness.metadata.clause sourceClauseMember)
      different point firstContains

end PeriodicOrthocrossing
end LeanTrominoes
