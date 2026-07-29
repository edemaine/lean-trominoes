import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTranslatedComponentCenters
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedContactTranslationBounds

/-!
# Periodic separation of retained noncarrier components

Two final occurrences generally come from different anchor-adjusted
translates of the finite retained drawing.  For noncarrier components, each
selected local route remains inside one standard planar-SAT macrocell.
After aligning physical shifts, distinct macrocell centers therefore give
continuous separation directly; equal centers are classified by the
translated-center results.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- The retained metadata lookup stored by a final segment witness supplies
the metadata validity certificate used by local component geometry. -/
theorem FinalGaugedSegmentOccurrenceWitness.metadata_retainedValid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    witness.routeWitness.metadata.RetainedValid formula := by
  have metadataMember :
      witness.routeWitness.metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    List.mem_iff_getElem?.mpr
      ⟨witness.routeWitness.metadataIndex,
        witness.routeWitness.metadataLookup⟩
  exact retainedDrawingPlanarSATClauseMetadata_valid
    formula metadataMember

/-- Selected routes in a translated first noncarrier macrocell and an
untranslated second noncarrier macrocell avoid one another whenever their
physical drawing-grid centers differ. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_localRoutes_avoidEachOther_of_macrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstCenter secondCenter shift : Cell)
    (firstCenterEq :
      first.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEq :
      second.source.component.macrocellCenter formula =
        some secondCenter)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (centersDifferent :
      Cell.add firstCenter
          ((drawing (PeriodicCNF.incidenceGraph formula)).periodTranslation
            shift) ≠
        secondCenter) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula shift).incidenceDrawing
          formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have firstNotCarrier :
      ¬∃ link, first.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at firstCenterEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at firstCenterEq
  have secondNotCarrier :
      ¬∃ link, second.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at secondCenterEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at secondCenterEq
  have firstOriginalValid :=
    first.valid_of_retainedValid_of_not_carrier
      firstValid firstNotCarrier
  have secondOriginalValid :=
    second.valid_of_retainedValid_of_not_carrier
      secondValid secondNotCarrier
  apply
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
  apply routesStrictlyAvoidEachOther_of_inPlanarSATMacrocells
    (firstCenter :=
      Cell.add firstCenter
        ((drawing graph).periodTranslation shift))
    (secondCenter := secondCenter)
  · intro point pointMember
    rw [DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
      at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨sourcePoint, sourcePointMember, pointEq⟩
    have sourceBounded :=
      first.localRoutePoints_inPlanarSATMacrocell
        wellFormed degree isLocal firstOriginalValid
        firstCenter firstCenterEq firstLiteralMember
        sourcePointMember
    have translatedBounded :=
      inPlanarSATMacrocell_translate
        (shift := shift)
        (drawingGridSize graph) sourceBounded
    subst point
    simpa [graph, carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale,
      add_comm, mul_assoc, mul_comm, mul_left_comm] using
        translatedBounded
  · intro point pointMember
    exact
      second.localRoutePoints_inPlanarSATMacrocell
        wellFormed degree isLocal secondOriginalValid
        secondCenter secondCenterEq secondLiteralMember pointMember
  · exact centersDifferent

/-- Route avoidance excludes continuous interior contact for any two
segments selected by flat `zipIdx` membership witnesses. -/
theorem
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_interiorsDisjoint
    {firstRoute secondRoute : List Cell}
    (avoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstRoute secondRoute)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstMember :
      firstSegment ∈ (gridPolylineSegments firstRoute).zipIdx)
    (secondMember :
      secondSegment ∈ (gridPolylineSegments secondRoute).zipIdx) :
    ¬GridSegment.InteriorsMeet firstSegment.1 secondSegment.1 := by
  have firstIndexLt :
      firstSegment.2 < (gridPolylineSegments firstRoute).length :=
    List.snd_lt_of_mem_zipIdx firstMember
  have secondIndexLt :
      secondSegment.2 < (gridPolylineSegments secondRoute).length :=
    List.snd_lt_of_mem_zipIdx secondMember
  let firstIndex : Fin (gridPolylineSegments firstRoute).length :=
    ⟨firstSegment.2, firstIndexLt⟩
  let secondIndex : Fin (gridPolylineSegments secondRoute).length :=
    ⟨secondSegment.2, secondIndexLt⟩
  have firstAt :
      (gridPolylineSegments firstRoute).get firstIndex =
        firstSegment.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp firstMember)).2
  have secondAt :
      (gridPolylineSegments secondRoute).get secondIndex =
        secondSegment.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp secondMember)).2
  simpa only [firstAt, secondAt] using
    avoid.1 firstIndex secondIndex

/-- Complete route avoidance also excludes contact between the relative
interior of a selected first segment and the closed extent of a selected
second segment. -/
theorem
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_avoidsInterior
    {firstRoute secondRoute : List Cell}
    (avoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstRoute secondRoute)
    {firstSegment secondSegment : GridSegment × Nat}
    (firstMember :
      firstSegment ∈ (gridPolylineSegments firstRoute).zipIdx)
    (secondMember :
      secondSegment ∈ (gridPolylineSegments secondRoute).zipIdx)
    {point : Cell}
    (firstContains : firstSegment.1.InteriorContains point) :
    ¬secondSegment.1.Contains point := by
  have firstIndexLt :
      firstSegment.2 < (gridPolylineSegments firstRoute).length :=
    List.snd_lt_of_mem_zipIdx firstMember
  have secondIndexLt :
      secondSegment.2 < (gridPolylineSegments secondRoute).length :=
    List.snd_lt_of_mem_zipIdx secondMember
  let firstIndex : Fin (gridPolylineSegments firstRoute).length :=
    ⟨firstSegment.2, firstIndexLt⟩
  let secondIndex : Fin (gridPolylineSegments secondRoute).length :=
    ⟨secondSegment.2, secondIndexLt⟩
  have firstAt :
      (gridPolylineSegments firstRoute).get firstIndex =
        firstSegment.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp firstMember)).2
  have secondAt :
      (gridPolylineSegments secondRoute).get secondIndex =
        secondSegment.1 :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp secondMember)).2
  intro secondContains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        secondContains with
    secondInterior | secondEndpoint
  · exact
      (avoid.1 firstIndex secondIndex)
        (by
          simpa only [firstAt, secondAt] using
            GridSegment.interiorsMeet_of_interiorContains
              firstContains secondInterior)
  · have endpointMember : point ∈ secondRoute := by
      have endpoints :=
        gridPolylineSegments_endpoints_mem
          (List.fst_mem_of_mem_zipIdx secondMember)
      rcases secondEndpoint with atStart | atFinish
      · exact atStart.symm ▸ endpoints.1
      · exact atFinish.symm ▸ endpoints.2
    rcases List.mem_iff_getElem.mp endpointMember with
      ⟨pointIndex, pointIndexLt, pointAt⟩
    let finitePointIndex : Fin secondRoute.length :=
      ⟨pointIndex, pointIndexLt⟩
    have finitePointAt :
        secondRoute.get finitePointIndex = point := by
      change secondRoute[pointIndex] = point
      exact pointAt
    exact
      (avoid.2.2.1 finitePointIndex firstIndex)
        (by
          simpa only [finitePointAt, firstAt] using firstContains)

/-- A witness's finite physical segment belongs directly to the local source
route named by its retained metadata. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.physicalSegment_mem_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    (witness.physicalSegment, indexed.segmentIndex) ∈
      (gridPolylineSegments
        ((witness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            witness.routeWitness.metadata.source.localClauseIndex
            witness.taggedLiteral.2)).zipIdx := by
  simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.routeWitness.metadataLookup] using
      witness.physicalSegmentMember

/-- Translating a witness's finite physical segment by a source period
translate puts it on the correspondingly translated local source route. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.physicalSegment_periodTranslate_mem_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (sourceShift : Cell) :
    (witness.physicalSegment.translate
        (carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift),
      indexed.segmentIndex) ∈
      (gridPolylineSegments
        (((witness.routeWitness.metadata.source.periodTranslate
          formula sourceShift).incidenceDrawing formula).routes
            witness.routeWitness.metadata.source.localClauseIndex
            witness.taggedLiteral.2)).zipIdx := by
  let offset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph sourceShift
  rw [
    DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
  change
    (witness.physicalSegment.translate offset,
        indexed.segmentIndex) ∈
      (gridPolylineSegments
        (translatePolyline offset
          ((witness.routeWitness.metadata.source.incidenceDrawing
            formula).routes
              witness.routeWitness.metadata.source.localClauseIndex
              witness.taggedLiteral.2))).zipIdx
  rw [show translatePolyline offset
        ((witness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            witness.routeWitness.metadata.source.localClauseIndex
            witness.taggedLiteral.2) =
      ((witness.routeWitness.metadata.source.incidenceDrawing
        formula).routes
          witness.routeWitness.metadata.source.localClauseIndex
          witness.taggedLiteral.2).map (Cell.add offset) by rfl,
    EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
    List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨(witness.physicalSegment, indexed.segmentIndex),
      witness.physicalSegment_mem_sourceRoute, rfl⟩

/-- Translating a segment first by a difference of lattice shifts and then
by the second shift equals translating it directly by the first shift. -/
theorem segment_translate_placement_sub_add
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (segment : GridSegment)
    (firstShift secondShift : Cell) :
    (segment.translate
        (placement.translation
          (Cell.sub firstShift secondShift))).translate
        (placement.translation secondShift) =
      segment.translate (placement.translation firstShift) := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases firstShift with ⟨firstX, firstY⟩
  rcases secondShift with ⟨secondX, secondY⟩
  simp only [GridSegment.translate,
    PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add, Cell.sub]
  congr 1 <;> apply Prod.ext <;> simp <;> ring

/-- Translating a segment by a source reindexing and then by the remaining
physical shift equals translating it directly by the physical shift. -/
theorem segment_translate_placement_add_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (segment : GridSegment)
    (physicalShift reindexShift : Cell) :
    (segment.translate
        (placement.translation reindexShift)).translate
        (placement.translation
          (Cell.sub physicalShift reindexShift)) =
      segment.translate (placement.translation physicalShift) := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases physicalShift with ⟨physicalX, physicalY⟩
  rcases reindexShift with ⟨reindexX, reindexY⟩
  simp only [GridSegment.translate,
    PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add, Cell.sub]
  congr 1 <;> apply Prod.ext <;> simp <;> ring

/-- An avoidance certificate between two independently translated local
sources transfers to the final periodic occurrences when the remaining
external shifts agree. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_two_periodTranslate_localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift)
    (routeAvoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        ((((first.routeWitness.metadata.source.periodTranslate formula
          firstSourceShift).incidenceDrawing formula).routes
            first.routeWitness.metadata.source.localClauseIndex
            first.taggedLiteral.2))
        ((((second.routeWitness.metadata.source.periodTranslate formula
          secondSourceShift).incidenceDrawing formula).routes
            second.routeWitness.metadata.source.localClauseIndex
            second.taggedLiteral.2))) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let firstOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph firstSourceShift
  let secondOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph secondSourceShift
  have rawDisjoint :
      ¬GridSegment.InteriorsMeet
        (first.physicalSegment.translate firstOffset)
        (second.physicalSegment.translate secondOffset) :=
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_interiorsDisjoint
      routeAvoid
      (by simpa only [firstOffset] using
        (first.physicalSegment_periodTranslate_mem_sourceRoute
          firstSourceShift))
      (by simpa only [secondOffset] using
        (second.physicalSegment_periodTranslate_mem_sourceRoute
          secondSourceShift))
  intro meet
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq,
    secondRepresentative.segmentEq] at meet
  change
    GridSegment.InteriorsMeet
      (first.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation first.physicalShift))
      (second.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation second.physicalShift)) at meet
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have firstOffsetEq :
      firstOffset =
        placement.translation firstSourceShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula firstSourceShift).symm
  have secondOffsetEq :
      secondOffset =
        placement.translation secondSourceShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula secondSourceShift).symm
  have firstAlignedEq :
      (first.physicalSegment.translate firstOffset).translate
          (placement.translation
            (Cell.sub first.physicalShift firstSourceShift)) =
        first.physicalSegment.translate
          (placement.translation first.physicalShift) := by
    rw [firstOffsetEq]
    exact segment_translate_placement_add_sub
      placement first.physicalSegment
      first.physicalShift firstSourceShift
  have secondAlignedEq :
      (second.physicalSegment.translate secondOffset).translate
          (placement.translation
            (Cell.sub second.physicalShift secondSourceShift)) =
        second.physicalSegment.translate
          (placement.translation second.physicalShift) := by
    rw [secondOffsetEq]
    exact segment_translate_placement_add_sub
      placement second.physicalSegment
      second.physicalShift secondSourceShift
  rw [← firstAlignedEq, ← secondAlignedEq,
    ← commonShiftEq] at meet
  exact rawDisjoint
    ((GridSegment.interiorsMeet_translate_both_iff
      (first.physicalSegment.translate firstOffset)
      (second.physicalSegment.translate secondOffset)
      (placement.translation
        (Cell.sub first.physicalShift firstSourceShift))).mp meet)

/-- An avoidance certificate between two independently translated local
sources also transfers the asymmetric interior-versus-closed contact
condition to the final periodic occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_two_periodTranslate_localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift)
    (routeAvoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        ((((first.routeWitness.metadata.source.periodTranslate formula
          firstSourceShift).incidenceDrawing formula).routes
            first.routeWitness.metadata.source.localClauseIndex
            first.taggedLiteral.2))
        ((((second.routeWitness.metadata.source.periodTranslate formula
          secondSourceShift).incidenceDrawing formula).routes
            second.routeWitness.metadata.source.localClauseIndex
            second.taggedLiteral.2)))
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let firstOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph firstSourceShift
  let secondOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph secondSourceShift
  have rawAvoid :
      ∀ {rawPoint : Cell},
        (first.physicalSegment.translate firstOffset).InteriorContains
            rawPoint →
          ¬(second.physicalSegment.translate secondOffset).Contains
            rawPoint :=
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_avoidsInterior
      routeAvoid
      (by simpa only [firstOffset] using
        (first.physicalSegment_periodTranslate_mem_sourceRoute
          firstSourceShift))
      (by simpa only [secondOffset] using
        (second.physicalSegment_periodTranslate_mem_sourceRoute
          secondSourceShift))
  intro secondContains
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq] at firstContains
  rw [secondRepresentative.segmentEq] at secondContains
  change
    (first.physicalSegment.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation first.physicalShift)).InteriorContains
      point at firstContains
  change
    (second.physicalSegment.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation second.physicalShift)).Contains
      point at secondContains
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have firstOffsetEq :
      firstOffset =
        placement.translation firstSourceShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula firstSourceShift).symm
  have secondOffsetEq :
      secondOffset =
        placement.translation secondSourceShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula secondSourceShift).symm
  have firstAlignedEq :
      (first.physicalSegment.translate firstOffset).translate
          (placement.translation
            (Cell.sub first.physicalShift firstSourceShift)) =
        first.physicalSegment.translate
          (placement.translation first.physicalShift) := by
    rw [firstOffsetEq]
    exact segment_translate_placement_add_sub
      placement first.physicalSegment
      first.physicalShift firstSourceShift
  have secondAlignedEq :
      (second.physicalSegment.translate secondOffset).translate
          (placement.translation
            (Cell.sub second.physicalShift secondSourceShift)) =
        second.physicalSegment.translate
          (placement.translation second.physicalShift) := by
    rw [secondOffsetEq]
    exact segment_translate_placement_add_sub
      placement second.physicalSegment
      second.physicalShift secondSourceShift
  rw [← firstAlignedEq] at firstContains
  rw [← secondAlignedEq, ← commonShiftEq] at secondContains
  let commonOffset :=
    placement.translation
      (Cell.sub first.physicalShift firstSourceShift)
  let normalizedPoint := Cell.sub point commonOffset
  have normalizedFirst :
      (first.physicalSegment.translate firstOffset).InteriorContains
        normalizedPoint := by
    apply
      (PeriodicGridDrawing.interiorContains_translate_iff
        (first.physicalSegment.translate firstOffset)
        commonOffset normalizedPoint).mp
    simpa [commonOffset, normalizedPoint, Cell.add, Cell.sub] using
      firstContains
  have normalizedSecond :
      (second.physicalSegment.translate secondOffset).Contains
        normalizedPoint := by
    apply
      (PeriodicGridDrawing.contains_translate_iff
        (second.physicalSegment.translate secondOffset)
        commonOffset normalizedPoint).mp
    simpa [commonOffset, normalizedPoint, Cell.add, Cell.sub] using
      secondContains
  exact rawAvoid normalizedFirst normalizedSecond

/-- Any avoidance certificate between the physically translated first local
route and the second local route transfers to the corresponding final
periodic segment occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (routeAvoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        ((((first.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub first.physicalShift second.physicalShift))
            |>.incidenceDrawing formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2))
        ((second.routeWitness.metadata.source.incidenceDrawing formula).routes
          second.routeWitness.metadata.source.localClauseIndex
          second.taggedLiteral.2)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  let offset :=
    carrierMacroPeriodTranslation formula.incidenceGraph reindexShift
  have firstTranslatedMember :
      (first.physicalSegment.translate offset,
          firstIndexed.segmentIndex) ∈
        (gridPolylineSegments
          (((first.routeWitness.metadata.source.periodTranslate
            formula reindexShift).incidenceDrawing formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2)).zipIdx := by
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    change
      (first.physicalSegment.translate offset,
          firstIndexed.segmentIndex) ∈
        (gridPolylineSegments
          (translatePolyline offset
            ((first.routeWitness.metadata.source.incidenceDrawing
              formula).routes
                first.routeWitness.metadata.source.localClauseIndex
                first.taggedLiteral.2))).zipIdx
    rw [show translatePolyline offset
          ((first.routeWitness.metadata.source.incidenceDrawing
            formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2) =
        ((first.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            first.routeWitness.metadata.source.localClauseIndex
            first.taggedLiteral.2).map (Cell.add offset) by rfl,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(first.physicalSegment, firstIndexed.segmentIndex),
        first.physicalSegment_mem_sourceRoute, rfl⟩
  have rawDisjoint :
      ¬GridSegment.InteriorsMeet
        (first.physicalSegment.translate offset)
        second.physicalSegment :=
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_interiorsDisjoint
      (by simpa only [reindexShift] using routeAvoid)
      firstTranslatedMember second.physicalSegment_mem_sourceRoute
  intro meet
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq,
    secondRepresentative.segmentEq] at meet
  change
    GridSegment.InteriorsMeet
      (first.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation first.physicalShift))
      (second.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation second.physicalShift)) at meet
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have offsetEq :
      offset = placement.translation reindexShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula reindexShift).symm
  have firstAlignedEq :
      (first.physicalSegment.translate offset).translate
          (placement.translation second.physicalShift) =
        first.physicalSegment.translate
          (placement.translation first.physicalShift) := by
    rw [offsetEq]
    exact segment_translate_placement_sub_add
      placement first.physicalSegment
      first.physicalShift second.physicalShift
  rw [← firstAlignedEq] at meet
  exact rawDisjoint
    ((GridSegment.interiorsMeet_translate_both_iff
      (first.physicalSegment.translate offset)
      second.physicalSegment
      (placement.translation second.physicalShift)).mp meet)

/-- A physically translated local-route avoidance certificate also
transfers the asymmetric interior-versus-closed contact condition. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_periodTranslate_localRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (routeAvoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        ((((first.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub first.physicalShift second.physicalShift))
            |>.incidenceDrawing formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2))
        ((second.routeWitness.metadata.source.incidenceDrawing formula).routes
          second.routeWitness.metadata.source.localClauseIndex
          second.taggedLiteral.2))
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  let offset :=
    carrierMacroPeriodTranslation formula.incidenceGraph reindexShift
  have firstTranslatedMember :
      (first.physicalSegment.translate offset,
          firstIndexed.segmentIndex) ∈
        (gridPolylineSegments
          (((first.routeWitness.metadata.source.periodTranslate
            formula reindexShift).incidenceDrawing formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2)).zipIdx := by
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    change
      (first.physicalSegment.translate offset,
          firstIndexed.segmentIndex) ∈
        (gridPolylineSegments
          (translatePolyline offset
            ((first.routeWitness.metadata.source.incidenceDrawing
              formula).routes
                first.routeWitness.metadata.source.localClauseIndex
                first.taggedLiteral.2))).zipIdx
    rw [show translatePolyline offset
          ((first.routeWitness.metadata.source.incidenceDrawing
            formula).routes
              first.routeWitness.metadata.source.localClauseIndex
              first.taggedLiteral.2) =
        ((first.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            first.routeWitness.metadata.source.localClauseIndex
            first.taggedLiteral.2).map (Cell.add offset) by rfl,
      EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(first.physicalSegment, firstIndexed.segmentIndex),
        first.physicalSegment_mem_sourceRoute, rfl⟩
  have rawAvoid :
      ∀ {rawPoint : Cell},
        (first.physicalSegment.translate offset).InteriorContains
            rawPoint →
          ¬second.physicalSegment.Contains rawPoint :=
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.taggedSegments_avoidsInterior
      (by simpa only [reindexShift] using routeAvoid)
      firstTranslatedMember second.physicalSegment_mem_sourceRoute
  intro secondContains
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq] at firstContains
  rw [secondRepresentative.segmentEq] at secondContains
  change
    (first.physicalSegment.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation first.physicalShift)).InteriorContains
      point at firstContains
  change
    (second.physicalSegment.translate
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).translation second.physicalShift)).Contains
      point at secondContains
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have offsetEq :
      offset = placement.translation reindexShift := by
    exact
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula reindexShift).symm
  have firstAlignedEq :
      (first.physicalSegment.translate offset).translate
          (placement.translation second.physicalShift) =
        first.physicalSegment.translate
          (placement.translation first.physicalShift) := by
    rw [offsetEq]
    exact segment_translate_placement_sub_add
      placement first.physicalSegment
      first.physicalShift second.physicalShift
  rw [← firstAlignedEq] at firstContains
  let commonOffset := placement.translation second.physicalShift
  let normalizedPoint := Cell.sub point commonOffset
  have normalizedFirst :
      (first.physicalSegment.translate offset).InteriorContains
        normalizedPoint := by
    apply
      (PeriodicGridDrawing.interiorContains_translate_iff
        (first.physicalSegment.translate offset)
        commonOffset normalizedPoint).mp
    simpa [commonOffset, normalizedPoint, Cell.add, Cell.sub] using
      firstContains
  have normalizedSecond :
      second.physicalSegment.Contains normalizedPoint := by
    apply
      (PeriodicGridDrawing.contains_translate_iff
        second.physicalSegment commonOffset normalizedPoint).mp
    simpa [commonOffset, normalizedPoint, Cell.add, Cell.sub] using
      secondContains
  exact rawAvoid normalizedFirst normalizedSecond

/-- If the aligned macrocell centers of two final noncarrier segment
occurrences differ, macrocell separation rules out continuous contact. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_noncarrier_macrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      first.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some firstCenter)
    (secondCenterEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some secondCenter)
    (centersDifferent :
      Cell.add firstCenter
          ((drawing formula.incidenceGraph).periodTranslation
            (Cell.sub first.physicalShift second.physicalShift)) ≠
        secondCenter) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  have routeAvoid :=
    first.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_macrocellCenters_ne
        wellFormed degree isLocal
        second.routeWitness.metadata
        first.metadata_retainedValid
        second.metadata_retainedValid
        firstCenter secondCenter reindexShift
        firstCenterEq secondCenterEq
        first.routeWitness.literalMember
        second.routeWitness.literalMember
        (by simpa only [reindexShift] using centersDifferent)
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
      formula first second
  simpa only [reindexShift] using routeAvoid

/-- If the aligned macrocell centers of two final noncarrier segment
occurrences differ, macrocell separation also excludes asymmetric
interior-versus-closed contact. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarrier_macrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      formula.incidenceGraph.IsWellFormed)
    (degree :
      formula.incidenceGraph.DegreeAtMost 3)
    (isLocal :
      formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstCenter secondCenter : Cell)
    (firstCenterEq :
      first.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some firstCenter)
    (secondCenterEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some secondCenter)
    (centersDifferent :
      Cell.add firstCenter
          ((drawing formula.incidenceGraph).periodTranslation
            (Cell.sub first.physicalShift second.physicalShift)) ≠
        secondCenter)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  have routeAvoid :=
    first.routeWitness.metadata
      |>.periodTranslate_localRoutes_avoidEachOther_of_macrocellCenters_ne
        wellFormed degree isLocal
        second.routeWitness.metadata
        first.metadata_retainedValid
        second.metadata_retainedValid
        firstCenter secondCenter reindexShift
        firstCenterEq secondCenterEq
        first.routeWitness.literalMember
        second.routeWitness.literalMember
        (by simpa only [reindexShift] using centersDifferent)
  apply
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_periodTranslate_localRoutesAvoidEachOther
      formula first second
  · simpa only [reindexShift] using routeAvoid
  · exact firstContains

/-- At one translated routed-variable site, an active source link and an
active target link using the same physical duplicator arm are the same
complete translated link. -/
theorem planarSATNodeLinkPeriodTranslate_eq_of_routedVariable_same_site_arm
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (sourceSite targetSite : VariableRouteSite Variable)
    (sourceLink targetLink :
      EqualityLink (PlanarSATNode Variable))
    (sourceLinkMember :
      sourceLink ∈ routedVariableLinksAt formula sourceSite)
    (targetLinkMember :
      targetLink ∈ routedVariableLinksAt formula targetSite)
    (shift : Cell)
    (siteEq :
      variableRouteSitePeriodTranslate sourceSite shift =
        targetSite)
    (armEq :
      sourceLink.first.duplicatorArm =
        targetLink.first.duplicatorArm) :
    planarSATNodeLinkPeriodTranslate
        formula.incidenceGraph sourceLink shift =
      targetLink := by
  rcases (mem_routedVariableNodes_iff
      formula sourceSite sourceLink.first).mp
      (by
        rcases List.mem_map.mp sourceLinkMember with
          ⟨taggedNode, taggedNodeMember, linkEq⟩
        subst sourceLink
        exact List.mem_of_mem_take
          (List.fst_mem_of_mem_zipIdx taggedNodeMember)) with
    ⟨sourceOccurrence, sourceOccurrenceMember,
      sourceFirstEq⟩
  rcases (mem_routedVariableNodes_iff
      formula targetSite targetLink.first).mp
      (by
        rcases List.mem_map.mp targetLinkMember with
          ⟨taggedNode, taggedNodeMember, linkEq⟩
        subst targetLink
        exact List.mem_of_mem_take
          (List.fst_mem_of_mem_zipIdx taggedNodeMember)) with
    ⟨targetOccurrence, targetOccurrenceMember,
      targetFirstEq⟩
  have sourceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula sourceSite sourceOccurrenceMember
  have targetData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula targetSite targetOccurrenceMember
  have sourceEdgeMember :=
    sourceOccurrence.edge_mem_of_mem_drawing formula sourceData.1
  have targetEdgeMember :=
    targetOccurrence.edge_mem_of_mem_drawing formula targetData.1
  let graph := formula.incidenceGraph
  let sourcePort :=
    targetPort sourceOccurrence.edge sourceOccurrence.edgeIndex
  let targetPort' :=
    targetPort targetOccurrence.edge targetOccurrence.edgeIndex
  have sourcePortMember : sourcePort ∈ allPorts graph :=
    targetPort_mem_allPorts graph sourceEdgeMember
  have targetPortMember : targetPort' ∈ allPorts graph :=
    targetPort_mem_allPorts graph targetEdgeMember
  have terminalArmEq :
      (sourceOccurrence.targetTerminal formula).duplicatorArm =
        (targetOccurrence.targetTerminal formula).duplicatorArm := by
    rw [sourceFirstEq, targetFirstEq] at armEq
    change
      (sourceOccurrence.targetTerminal formula).duplicatorArm =
        (targetOccurrence.targetTerminal formula).duplicatorArm
      at armEq
    exact armEq
  rw [sourceOccurrence.targetTerminal_duplicatorArm formula,
    targetOccurrence.targetTerminal_duplicatorArm formula]
      at terminalArmEq
  have rankEq :
      portRank graph sourcePort =
        portRank graph targetPort' := by
    apply targetDuplicatorArm_injective_below_three
    · exact portRank_lt_three degree sourcePortMember
    · exact portRank_lt_three degree targetPortMember
    · exact terminalArmEq
  have sourceAtomEq :
      sourceOccurrence.incidence.literal.atom = sourceSite.1 := by
    simpa [CNFRouteOccurrence.variableOccurrence] using
      congrArg Prod.fst sourceData.2
  have targetAtomEq :
      targetOccurrence.incidence.literal.atom = targetSite.1 := by
    simpa [CNFRouteOccurrence.variableOccurrence] using
      congrArg Prod.fst targetData.2
  have siteAtomEq : sourceSite.1 = targetSite.1 := by
    simpa [variableRouteSitePeriodTranslate] using
      congrArg Prod.fst siteEq
  have targetVertexEq :
      sourcePort.vertex = targetPort'.vertex := by
    dsimp [sourcePort, targetPort']
    change
      CNFVertex.variable
          sourceOccurrence.incidence.literal.atom =
        CNFVertex.variable
          targetOccurrence.incidence.literal.atom
    rw [sourceAtomEq, targetAtomEq, siteAtomEq]
  have portXEq :
      portX graph sourcePort = portX graph targetPort' := by
    unfold portX
    rw [targetVertexEq, rankEq]
  have portEq : sourcePort = targetPort' :=
    portX_injective_on_allPorts
      wellFormed degree sourcePortMember targetPortMember portXEq
  have edgeIndexEq :
      sourceOccurrence.edgeIndex =
        targetOccurrence.edgeIndex :=
    congrArg GraphPort.edgeIndex portEq
  have incidenceEq :
      sourceOccurrence.incidence =
        targetOccurrence.incidence :=
    CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
      formula sourceData.1 targetData.1 edgeIndexEq
  have edgeEq :
      sourceOccurrence.edge = targetOccurrence.edge :=
    congrArg CNFIncidence.edge incidenceEq
  have translatedSourceSiteEq :
      (sourceOccurrence.periodTranslate shift).variableOccurrence =
        targetSite := by
    rw [CNFRouteOccurrence.variableOccurrence_periodTranslate,
      sourceData.2, siteEq]
  have translatedTargetEq :
      Cell.add (Cell.add sourceOccurrence.translate shift)
          sourceOccurrence.edge.offset =
        Cell.add targetOccurrence.translate
          targetOccurrence.edge.offset := by
    have translatedTargetEq' :=
      congrArg Prod.snd
        (translatedSourceSiteEq.trans targetData.2.symm)
    change
      Cell.add (Cell.add sourceOccurrence.translate shift)
          (sourceOccurrence.periodTranslate shift).edge.offset =
        Cell.add targetOccurrence.translate
          targetOccurrence.edge.offset
      at translatedTargetEq'
    have edgePeriodTranslate :
      (sourceOccurrence.periodTranslate shift).edge =
        sourceOccurrence.edge := rfl
    rw [edgePeriodTranslate] at translatedTargetEq'
    exact translatedTargetEq'
  have translateEq :
      Cell.add sourceOccurrence.translate shift =
        targetOccurrence.translate := by
    rw [edgeEq] at translatedTargetEq
    exact Cell.add_right_injective
      targetOccurrence.edge.offset translatedTargetEq
  have occurrenceEq :
      sourceOccurrence.periodTranslate shift =
        targetOccurrence := by
    rcases sourceOccurrence with
      ⟨sourceIncidence, sourceEdgeIndex, sourceTranslate⟩
    rcases targetOccurrence with
      ⟨targetIncidence, targetEdgeIndex, targetTranslate⟩
    simp only at incidenceEq edgeIndexEq translateEq
    simp only [CNFRouteOccurrence.periodTranslate,
      CNFRouteOccurrence.mk.injEq]
    exact ⟨incidenceEq, edgeIndexEq, translateEq⟩
  have firstEndpointEq :
      sourceLink.first.periodTranslate graph shift =
        targetLink.first := by
    calc
      sourceLink.first.periodTranslate graph shift =
          (PlanarSATNode.carrier
            (CarrierNode.terminal
              (sourceOccurrence.targetTerminal formula))).periodTranslate
                graph shift := by rw [sourceFirstEq]
      _ =
          PlanarSATNode.carrier
            (CarrierNode.terminal
              ((sourceOccurrence.periodTranslate shift).targetTerminal
                formula)) := rfl
      _ = targetLink.first := by
        rw [occurrenceEq, targetFirstEq]
  have secondEndpointEq :
      (planarSATNodeLinkPeriodTranslate
          graph sourceLink shift).second =
        targetLink.second := by
    rw [planarSATNodeLinkPeriodTranslate,
      routedVariableLinksAt_second
        formula sourceSite sourceLinkMember,
      routedVariableLinksAt_second
        formula targetSite targetLinkMember]
    simpa [PlanarSATNode.periodTranslate] using siteEq
  have positionsEq :
      (planarSATNodeLinkPeriodTranslate
          graph sourceLink shift).positions =
        targetLink.positions := by
    rw [planarSATNodeLinkPeriodTranslate,
      routedVariableLink_positions
        formula sourceSite sourceLinkMember,
      routedVariableLink_positions
        formula targetSite targetLinkMember,
      ← siteEq,
      routedVariableEqualityPositions_periodTranslate,
      armEq]
  rcases sourceLink with
    ⟨sourceFirst, sourceSecond, sourcePositions⟩
  rcases targetLink with
    ⟨targetFirst, targetSecond, targetPositions⟩
  simp only [planarSATNodeLinkPeriodTranslate] at firstEndpointEq secondEndpointEq positionsEq ⊢
  subst targetFirst
  subst targetSecond
  subst targetPositions
  rfl

/-- A source whose component is a routed-variable component is itself a
routed-variable source, with only its arm and local clause indices omitted
by the component projection. -/
theorem
    DrawingPlanarSATClauseSource.exists_eq_routedVariable_of_component_eq
    {Variable : Type*}
    (source : DrawingPlanarSATClauseSource Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (componentEq :
      source.component = .routedVariable site arm link) :
    ∃ armIndex localClauseIndex,
      source =
        .routedVariable site armIndex arm link localClauseIndex := by
  cases source <;>
    simp_all [DrawingPlanarSATClauseSource.component]

/-- Recover the unshifted routed-variable source data from a translated
component equality. -/
theorem
    DrawingPlanarSATClauseSource.exists_eq_routedVariable_of_periodTranslate_component_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (componentEq :
      (source.periodTranslate formula shift).component =
        .routedVariable site arm link) :
    ∃ sourceSite armIndex sourceLink localClauseIndex,
      source =
          .routedVariable sourceSite armIndex arm sourceLink
            localClauseIndex ∧
        variableRouteSitePeriodTranslate sourceSite shift = site ∧
        planarSATNodeLinkPeriodTranslate formula.incidenceGraph
            sourceLink shift =
          link := by
  cases source <;>
    simp_all [DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.component]

/-- When two translated noncarrier components coincide at a variable site
but use distinct duplicator arms, the two selected local routes avoid one
another. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_localRoutes_avoidEachOther_of_routedVariable_arms_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift : Cell)
    (site : VariableRouteSite Variable)
    (firstArm secondArm : DuplicatorArm)
    (firstLink secondLink :
      EqualityLink (PlanarSATNode Variable))
    (firstComponentEq :
      (first.source.periodTranslate formula shift).component =
        .routedVariable site firstArm firstLink)
    (secondComponentEq :
      second.source.component =
        .routedVariable site secondArm secondLink)
    (differentArms : firstArm ≠ secondArm)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula shift).incidenceDrawing
          formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases second with ⟨secondClause, secondSource⟩
  rcases
      firstSource
        |>.exists_eq_routedVariable_of_periodTranslate_component_eq
          formula shift site firstArm firstLink firstComponentEq with
    ⟨sourceSite, firstArmIndex, sourceLink, firstClauseIndex,
      firstSourceEq, sourceSiteEq, sourceLinkEq⟩
  rcases
      secondSource.exists_eq_routedVariable_of_component_eq
        site secondArm secondLink secondComponentEq with
    ⟨secondArmIndex, secondClauseIndex, secondSourceEq⟩
  have firstValid' := firstValid
  have secondValid' := secondValid
  rw [firstSourceEq] at firstValid'
  rw [secondSourceEq] at secondValid'
  have firstClauseIndexLt : firstClauseIndex < 2 :=
    drawingPlanarSATRoutedVariableFormulaAt_clauseIndex_lt_two
      sourceLink firstValid'.2.2.2
  have secondClauseIndexLt : secondClauseIndex < 2 :=
    drawingPlanarSATRoutedVariableFormulaAt_clauseIndex_lt_two
      secondLink secondValid'.2.2.2
  have firstLiteralIndexLt : firstLiteralIndex < 2 :=
    drawingPlanarSATRoutedVariableFormulaAt_literalIndex_lt_two
      sourceLink firstValid'.2.2.2 firstLiteralMember
  have secondLiteralIndexLt : secondLiteralIndex < 2 :=
    drawingPlanarSATRoutedVariableFormulaAt_literalIndex_lt_two
      secondLink secondValid'.2.2.2 secondLiteralMember
  have avoid :=
    drawingPlanarSATRoutedVariableIncidenceDrawing_routesAvoidEachOther_of_arms_ne
      formula site firstArm secondArm firstLink secondLink
      differentArms firstClauseIndex secondClauseIndex
      firstLiteralIndex secondLiteralIndex
      firstClauseIndexLt secondClauseIndexLt
      firstLiteralIndexLt secondLiteralIndexLt
  simpa [firstSourceEq, secondSourceEq,
    DrawingPlanarSATClauseSource.periodTranslate,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex,
    sourceSiteEq, sourceLinkEq] using avoid

/-- The exceptional equal-center routed-variable case is exact component
alignment when both sources use the same duplicator arm. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_component_eq_of_routedVariable_same_arm
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift : Cell)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (firstLink secondLink :
      EqualityLink (PlanarSATNode Variable))
    (firstComponentEq :
      (first.source.periodTranslate formula shift).component =
        .routedVariable site arm firstLink)
    (secondComponentEq :
      second.source.component =
        .routedVariable site arm secondLink) :
    second.source.component =
      (first.source.periodTranslate formula shift).component := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases second with ⟨secondClause, secondSource⟩
  rcases
      firstSource
        |>.exists_eq_routedVariable_of_periodTranslate_component_eq
          formula shift site arm firstLink firstComponentEq with
    ⟨sourceSite, firstArmIndex, sourceLink, firstClauseIndex,
      firstSourceEq, sourceSiteEq, sourceLinkEq⟩
  rcases
      secondSource.exists_eq_routedVariable_of_component_eq
        site arm secondLink secondComponentEq with
    ⟨secondArmIndex, secondClauseIndex, secondSourceEq⟩
  have firstValid' := firstValid
  have secondValid' := secondValid
  rw [firstSourceEq] at firstValid'
  rw [secondSourceEq] at secondValid'
  have sourceLinkMember :
      sourceLink ∈ routedVariableLinksAt formula sourceSite :=
    List.fst_mem_of_mem_zipIdx firstValid'.2.1
  have secondLinkMember :
      secondLink ∈ routedVariableLinksAt formula site :=
    List.fst_mem_of_mem_zipIdx secondValid'.2.1
  have classifiedArmsEq :
      sourceLink.first.duplicatorArm =
        secondLink.first.duplicatorArm :=
    firstValid'.2.2.1.symm.trans secondValid'.2.2.1
  have translatedLinkEq :
      planarSATNodeLinkPeriodTranslate formula.incidenceGraph
          sourceLink shift =
        secondLink :=
    planarSATNodeLinkPeriodTranslate_eq_of_routedVariable_same_site_arm
      formula wellFormed degree sourceSite site
      sourceLink secondLink sourceLinkMember secondLinkMember
      shift sourceSiteEq classifiedArmsEq
  have linksEq : firstLink = secondLink :=
    sourceLinkEq.symm.trans translatedLinkEq
  rw [firstComponentEq, secondComponentEq, linksEq]

/-- Any two distinct final occurrences selected from noncarrier local
components have disjoint continuous segment interiors, even when their
finite representatives use different physical gauge shifts. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_noncarriers
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (firstNotCarrier :
      ¬∃ link,
        first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ link,
        second.routeWitness.metadata.source.component = .carrier link)
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
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula firstNotCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      second.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula secondNotCarrier with
    ⟨secondCenter, secondCenterEq⟩
  by_cases centersEqual :
      Cell.add firstCenter
          ((drawing formula.incidenceGraph).periodTranslation
            reindexShift) =
        secondCenter
  · have firstTranslatedCenterEq :
        ((first.routeWitness.metadata.source.periodTranslate
            formula reindexShift).component
          |>.macrocellCenter formula) =
          some secondCenter := by
      rw [DrawingPlanarSATClauseSource.component_periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
        firstCenterEq]
      exact congrArg some centersEqual
    have classification :=
      retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
        formula wellFormed degree isLocal
        first.routeWitness.metadata second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        reindexShift secondCenter
        firstTranslatedCenterEq secondCenterEq
    rcases classification with componentAlignment | exception
    · apply
        retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_component_aligns_second
          formula wellFormed degree isLocal clausesNonempty
          first second
      · simpa only [reindexShift] using componentAlignment
      · exact different
    · rcases exception with
        ⟨site, firstArm, firstLink, secondArm, secondLink,
          firstComponentEq, secondComponentEq⟩
      by_cases armsEqual : firstArm = secondArm
      · subst secondArm
        have componentAlignment :=
          first.routeWitness.metadata
            |>.periodTranslate_component_eq_of_routedVariable_same_arm
              wellFormed degree second.routeWitness.metadata
              first.metadata_retainedValid
              second.metadata_retainedValid
              reindexShift site firstArm firstLink secondLink
              firstComponentEq secondComponentEq
        apply
          retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_component_aligns_second
            formula wellFormed degree isLocal clausesNonempty
            first second
        · simpa only [reindexShift] using componentAlignment
        · exact different
      · have routeAvoid :=
          first.routeWitness.metadata
            |>.periodTranslate_localRoutes_avoidEachOther_of_routedVariable_arms_ne
              second.routeWitness.metadata
              first.metadata_retainedValid
              second.metadata_retainedValid
              reindexShift site firstArm secondArm firstLink secondLink
              firstComponentEq secondComponentEq armsEqual
              first.routeWitness.literalMember
              second.routeWitness.literalMember
        apply
          retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
            formula first second
        simpa only [reindexShift] using routeAvoid
  · apply
      retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_noncarrier_macrocellCenters_ne
        formula wellFormed degree isLocal first second
        firstCenter secondCenter firstCenterEq secondCenterEq
    simpa only [reindexShift] using centersEqual

/-- Any two distinct final occurrences selected from noncarrier local
components satisfy asymmetric interior-versus-closed avoidance, even when
their finite representatives use different physical gauge shifts. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarriers
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
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
    (firstNotCarrier :
      ¬∃ link,
        first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ link,
        second.routeWitness.metadata.source.component = .carrier link)
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
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula firstNotCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      second.routeWitness.metadata.source.component
        |>.exists_macrocellCenter_of_not_carrier
          formula secondNotCarrier with
    ⟨secondCenter, secondCenterEq⟩
  by_cases centersEqual :
      Cell.add firstCenter
          ((drawing formula.incidenceGraph).periodTranslation
            reindexShift) =
        secondCenter
  · have firstTranslatedCenterEq :
        ((first.routeWitness.metadata.source.periodTranslate
            formula reindexShift).component
          |>.macrocellCenter formula) =
          some secondCenter := by
      rw [DrawingPlanarSATClauseSource.component_periodTranslate,
        DrawingPlanarSATComponent.macrocellCenter_periodTranslate,
        firstCenterEq]
      exact congrArg some centersEqual
    have classification :=
      retainedNoncarrierComponents_periodTranslate_eq_or_routedVariable_of_center_eq
        formula wellFormed degree isLocal
        first.routeWitness.metadata second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        reindexShift secondCenter
        firstTranslatedCenterEq secondCenterEq
    rcases classification with componentAlignment | exception
    · apply
        retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_component_aligns_second
          formula wellFormed degree isLocal clausesNonempty
          first second
      · simpa only [reindexShift] using componentAlignment
      · exact different
      · exact firstContains
    · rcases exception with
        ⟨site, firstArm, firstLink, secondArm, secondLink,
          firstComponentEq, secondComponentEq⟩
      by_cases armsEqual : firstArm = secondArm
      · subst secondArm
        have componentAlignment :=
          first.routeWitness.metadata
            |>.periodTranslate_component_eq_of_routedVariable_same_arm
              wellFormed degree second.routeWitness.metadata
              first.metadata_retainedValid
              second.metadata_retainedValid
              reindexShift site firstArm firstLink secondLink
              firstComponentEq secondComponentEq
        apply
          retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_component_aligns_second
            formula wellFormed degree isLocal clausesNonempty
            first second
        · simpa only [reindexShift] using componentAlignment
        · exact different
        · exact firstContains
      · have routeAvoid :=
          first.routeWitness.metadata
            |>.periodTranslate_localRoutes_avoidEachOther_of_routedVariable_arms_ne
              second.routeWitness.metadata
              first.metadata_retainedValid
              second.metadata_retainedValid
              reindexShift site firstArm secondArm firstLink secondLink
              firstComponentEq secondComponentEq armsEqual
              first.routeWitness.literalMember
              second.routeWitness.literalMember
        apply
          retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_periodTranslate_localRoutesAvoidEachOther
            formula first second
        · simpa only [reindexShift] using routeAvoid
        · exact firstContains
  · apply
      retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_noncarrier_macrocellCenters_ne
        formula wellFormed degree isLocal first second
        firstCenter secondCenter firstCenterEq secondCenterEq
    · simpa only [reindexShift] using centersEqual
    · exact firstContains

end PeriodicOrthocrossing
end LeanTrominoes
