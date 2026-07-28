import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceRouteTranslation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCommonShiftRepresentatives

/-!
# Reindexing final occurrences through translated retained metadata

The orbit-specific part of periodic planarity is to find a retained metadata
entry for a physical period translate of one source.  Once such an entry is
known, the remaining work is uniform: local clause and literal indices are
unchanged, route equivariance translates the same indexed segment, and the
opposite adjustment of the external occurrence shift preserves its physical
position.

This file packages the small orbit witness and performs that generic
construction, producing exactly the common-shift representative consumed by
the finite-planarity transfer theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Retained metadata realizing a physical period translate of the source
behind one final segment occurrence, at the same literal presentation
index. -/
structure FinalGaugedSegmentMetadataReindexing
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (reindexShift : Cell) where
  targetMetadata : DrawingPlanarSATClauseMetadata Variable
  targetMetadataIndex : Nat
  targetMetadataLookup :
    (retainedDrawingPlanarSATClauseMetadata formula)[
        targetMetadataIndex]? =
      some targetMetadata
  targetLiteral : PlanarSATVariable Variable × Bool
  targetLiteralMember :
    (targetLiteral, witness.taggedLiteral.2) ∈
      targetMetadata.clause.literals.zipIdx
  targetSourceEq :
    targetMetadata.source =
      witness.routeWitness.metadata.source.periodTranslate
        formula reindexShift

/-- The physical placement period is exactly the refined macro-period used
by source translation. -/
theorem
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (shift : Cell) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).translation shift =
      carrierMacroPeriodTranslation
        (PeriodicCNF.incidenceGraph formula) shift := by
  rcases shift with ⟨shiftX, shiftY⟩
  simp [retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement,
    drawingPeriodicPlanarSATPlacement,
    PeriodicVariablePlacement.translation,
    carrierMacroPeriodTranslation,
    planarMacroScale, Cell.scale]

/-- Translating a segment's source by `reindexShift` and subtracting the
same shift from its external occurrence leaves the physical segment
unchanged. -/
private theorem reindexedSegment_translate_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (segment : GridSegment)
    (physicalShift reindexShift : Cell) :
    (segment.translate (placement.translation reindexShift)).translate
        (placement.translation
          (Cell.sub physicalShift reindexShift)) =
      segment.translate (placement.translation physicalShift) := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases physicalShift with ⟨physicalX, physicalY⟩
  rcases reindexShift with ⟨reindexX, reindexY⟩
  simp only [GridSegment.translate,
    PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add, Cell.sub]
  congr 1 <;> apply Prod.ext <;> simp <;> ring

/-- A metadata lookup selects the same local source route used by the
assembled retained drawing. -/
private theorem retainedLocalRoute_eq_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (metadataIndex : Nat)
    (literal : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (metadataLookup :
      (retainedDrawingPlanarSATClauseMetadata formula)[metadataIndex]? =
        some metadata) :
    (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
        (metadataPhysicalIncidence
          metadata metadataIndex literal literalIndex) =
      (metadata.source.incidenceDrawing formula).routes
        metadata.source.localClauseIndex literalIndex := by
  simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    metadataLookup]

/-- Any translated retained-metadata witness yields a finite representative
at the correspondingly adjusted common physical shift. -/
theorem
    FinalGaugedSegmentMetadataReindexing.exists_commonShiftRepresentative
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift reindexShift : Cell}
    {witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift}
    (reindexing :
      FinalGaugedSegmentMetadataReindexing witness reindexShift) :
    Nonempty
      (FinalGaugedSegmentCommonShiftRepresentative
        formula indexed shift
          (Cell.sub witness.physicalShift reindexShift)) := by
  let sourceMetadata := witness.routeWitness.metadata
  let sourceIncidence :=
    metadataPhysicalIncidence
      sourceMetadata witness.routeWitness.metadataIndex
      witness.routeWitness.literal witness.taggedLiteral.2
  let targetIncidence :=
    metadataPhysicalIncidence
      reindexing.targetMetadata reindexing.targetMetadataIndex
      reindexing.targetLiteral witness.taggedLiteral.2
  have targetIncidenceMem :
      targetIncidence ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences := by
    exact metadataPhysicalIncidence_mem
      formula reindexing.targetMetadata
      reindexing.targetMetadataIndex
      reindexing.targetLiteral witness.taggedLiteral.2
      reindexing.targetMetadataLookup
      reindexing.targetLiteralMember
  rcases List.mem_iff_getElem.mp targetIncidenceMem with
    ⟨targetIncidenceIndex, targetIncidenceIndexLt,
      targetIncidenceAtEq⟩
  have targetIncidenceMember :
      (targetIncidence, targetIncidenceIndex) ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).incidences.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact
      ⟨targetIncidenceIndexLt,
        targetIncidenceAtEq⟩
  let offset :=
    carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) reindexShift
  have sourceRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          sourceIncidence =
        (sourceMetadata.source.incidenceDrawing formula).routes
          sourceMetadata.source.localClauseIndex
          witness.taggedLiteral.2 := by
    exact retainedLocalRoute_eq_sourceRoute
      formula sourceMetadata witness.routeWitness.metadataIndex
      witness.routeWitness.literal witness.taggedLiteral.2
      witness.routeWitness.metadataLookup
  have targetRouteEq :
      (retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          targetIncidence =
        translatePolyline offset
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            sourceIncidence) := by
    rw [retainedLocalRoute_eq_sourceRoute
      formula reindexing.targetMetadata
        reindexing.targetMetadataIndex
        reindexing.targetLiteral witness.taggedLiteral.2
        reindexing.targetMetadataLookup,
      reindexing.targetSourceEq,
      DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate,
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate,
      sourceRouteEq]
  let targetSegment := witness.physicalSegment.translate offset
  have targetSegmentMember :
      (targetSegment, indexed.segmentIndex) ∈
        (gridPolylineSegments
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            targetIncidence)).zipIdx := by
    rw [targetRouteEq]
    change
      (witness.physicalSegment.translate offset,
          indexed.segmentIndex) ∈
        (gridPolylineSegments
          (translatePolyline offset
            ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
              sourceIncidence))).zipIdx
    rw [show translatePolyline offset
          ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
            sourceIncidence) =
        ((retainedDrawingPlanarSATLocalIncidenceDrawing formula).routeAt
          sourceIncidence).map (Cell.add offset) by rfl,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(witness.physicalSegment, indexed.segmentIndex),
        by simpa only [sourceIncidence] using
          witness.physicalSegmentMember,
        rfl⟩
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have offsetEq :
      offset = placement.translation reindexShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula reindexShift).symm
  have targetPhysicalEq :
      targetSegment.translate
          (placement.translation
            (Cell.sub witness.physicalShift reindexShift)) =
        witness.physicalSegment.translate
          (placement.translation witness.physicalShift) := by
    rw [show targetSegment =
        witness.physicalSegment.translate
          (placement.translation reindexShift) by
      simpa only [targetSegment] using
        congrArg
          (fun translate =>
            witness.physicalSegment.translate translate)
          offsetEq]
    exact reindexedSegment_translate_sub
      placement witness.physicalSegment
      witness.physicalShift reindexShift
  let original := witness.toCommonShiftRepresentative
  refine ⟨{
    physicalIncidence := targetIncidence
    physicalIncidenceIndex := targetIncidenceIndex
    physicalIncidenceMember := targetIncidenceMember
    physicalSegment := targetSegment
    physicalSegmentMember := targetSegmentMember
    segmentEq := ?_
  }⟩
  calc
    indexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation shift) =
        witness.physicalSegment.translate
          (placement.translation witness.physicalShift) := by
      simpa only [original, placement,
        FinalGaugedSegmentOccurrenceWitness.toCommonShiftRepresentative]
        using original.segmentEq
    _ =
        targetSegment.translate
          (placement.translation
            (Cell.sub witness.physicalShift reindexShift)) :=
      targetPhysicalEq.symm

end PeriodicOrthocrossing
end LeanTrominoes
