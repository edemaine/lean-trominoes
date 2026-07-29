import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointReindexingInjectivity

/-!
# Route-point contacts from translated local-route avoidance

The component geometry used for continuous planarity proves the stronger
finite predicate `RoutesAvoidEachOther`.  This file transfers its
endpoint-contact clause directly to two final periodic route-point
occurrences, allowing the two physical sources to be translated
independently as long as their remaining external shifts agree.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A route-point witness's physical point belongs, at the same syntactic
index, to the local source route named by its retained metadata. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.physicalPoint_mem_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    (witness.physicalPoint, indexed.pointIndex) ∈
      (((witness.segmentWitness.routeWitness.metadata.source.incidenceDrawing
        formula).routes
          witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
          witness.segmentWitness.taggedLiteral.2).zipIdx) := by
  simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.segmentWitness.routeWitness.metadataLookup] using
      witness.physicalPointMember

/-- Translating a physical route point by a source period shift puts it on
the correspondingly translated local source route without changing its
within-route index. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.physicalPoint_periodTranslate_mem_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift)
    (sourceShift : Cell) :
    (Cell.add
        (carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift)
        witness.physicalPoint,
      indexed.pointIndex) ∈
      ((((witness.segmentWitness.routeWitness.metadata.source.periodTranslate
        formula sourceShift).incidenceDrawing formula).routes
          witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
          witness.segmentWitness.taggedLiteral.2).zipIdx) := by
  let offset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph sourceShift
  rw [
    DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
  change
    (Cell.add offset witness.physicalPoint, indexed.pointIndex) ∈
      (translatePolyline offset
        ((witness.segmentWitness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
            witness.segmentWitness.taggedLiteral.2)).zipIdx
  rw [show translatePolyline offset
        ((witness.segmentWitness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
            witness.segmentWitness.taggedLiteral.2) =
      ((witness.segmentWitness.routeWitness.metadata.source.incidenceDrawing
        formula).routes
          witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
          witness.segmentWitness.taggedLiteral.2).map (Cell.add offset) by rfl,
    List.zipIdx_map]
  exact List.mem_map.mpr
    ⟨(witness.physicalPoint, indexed.pointIndex),
      witness.physicalPoint_mem_sourceRoute, rfl⟩

/-- The physical local route selected by a final route-point witness is
simple in the retained finite drawing. -/
theorem
    FinalGaugedRoutePointOccurrenceWitness.physicalRoute_isSimple
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
    {indexed : IndexedRoutePoint}
    {shift : Cell}
    (witness :
      FinalGaugedRoutePointOccurrenceWitness formula indexed shift) :
    LocalIncidenceDrawing.RouteIsSimple
      (((witness.segmentWitness.routeWitness.metadata.source.incidenceDrawing
        formula).routes
          witness.segmentWitness.routeWitness.metadata.source.localClauseIndex
          witness.segmentWitness.taggedLiteral.2)) := by
  let finiteDrawing :=
    retainedDrawingPlanarSATLocalIncidenceDrawing formula
  have finitePlanar :
      finiteDrawing.IsPlanar :=
    retainedDrawingPlanarSATLocalIncidenceDrawing_isPlanar
      formula wellFormed degree isLocal clausesNonempty
  have incidenceIndexLt :
      witness.segmentWitness.physicalIncidenceIndex <
        finiteDrawing.incidences.length :=
    List.snd_lt_of_mem_zipIdx
      witness.segmentWitness.physicalIncidenceMember
  let incidenceIndex : Fin finiteDrawing.incidences.length :=
    ⟨witness.segmentWitness.physicalIncidenceIndex,
      incidenceIndexLt⟩
  have incidenceLookup :=
    (List.mem_zipIdx_iff_getElem?).mp
      witness.segmentWitness.physicalIncidenceMember
  have incidenceAt :
      finiteDrawing.incidenceAt incidenceIndex =
        metadataPhysicalIncidence
          witness.segmentWitness.routeWitness.metadata
          witness.segmentWitness.routeWitness.metadataIndex
          witness.segmentWitness.routeWitness.literal
          witness.segmentWitness.taggedLiteral.2 := by
    exact (List.getElem?_eq_some_iff.mp incidenceLookup).2
  have simple := finitePlanar.1 incidenceIndex
  change
    LocalIncidenceDrawing.RouteIsSimple
      (finiteDrawing.routeAt
        (finiteDrawing.incidenceAt incidenceIndex)) at simple
  rw [incidenceAt] at simple
  simpa [finiteDrawing,
    retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.segmentWitness.routeWitness.metadataLookup] using simple

/-- Translating a route point by a source shift and then by the remaining
physical shift equals translating it directly by the physical shift. -/
private theorem point_add_placement_add_sub
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (point : Cell)
    (physicalShift sourceShift : Cell) :
    Cell.add
        (Cell.add point (placement.translation sourceShift))
        (placement.translation
          (Cell.sub physicalShift sourceShift)) =
      Cell.add point (placement.translation physicalShift) := by
  rcases point with ⟨pointX, pointY⟩
  rcases physicalShift with ⟨physicalX, physicalY⟩
  rcases sourceShift with ⟨sourceX, sourceY⟩
  simp only [PeriodicVariablePlacement.translation,
    Cell.scale, Cell.add, Cell.sub, Prod.mk.injEq]
  constructor <;> ring

/-- A translated local-route avoidance certificate transfers its
endpoint-contact clause to the corresponding final periodic route points. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_routePointsAreEndpoints_of_two_periodTranslate_localRoutesAvoidEachOther
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
    {firstIndexed secondIndexed : IndexedRoutePoint}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedRoutePointOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedRoutePointOccurrenceWitness
        formula secondIndexed secondShift)
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.segmentWitness.physicalShift firstSourceShift =
        Cell.sub second.segmentWitness.physicalShift secondSourceShift)
    (routeAvoid :
      EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        ((((first.segmentWitness.routeWitness.metadata.source.periodTranslate
          formula firstSourceShift).incidenceDrawing formula).routes
            first.segmentWitness.routeWitness.metadata.source.localClauseIndex
            first.segmentWitness.taggedLiteral.2))
        ((((second.segmentWitness.routeWitness.metadata.source.periodTranslate
          formula secondSourceShift).incidenceDrawing formula).routes
            second.segmentWitness.routeWitness.metadata.source.localClauseIndex
            second.segmentWitness.taggedLiteral.2)))
    (equal :
      Cell.add firstIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift) =
        Cell.add secondIndexed.point
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift)) :
    firstIndexed.IsEndpoint ∧ secondIndexed.IsEndpoint := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let firstOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph firstSourceShift
  let secondOffset :=
    carrierMacroPeriodTranslation
      formula.incidenceGraph secondSourceShift
  let firstRoute :=
    (((first.segmentWitness.routeWitness.metadata.source.periodTranslate
      formula firstSourceShift).incidenceDrawing formula).routes
        first.segmentWitness.routeWitness.metadata.source.localClauseIndex
        first.segmentWitness.taggedLiteral.2)
  let secondRoute :=
    (((second.segmentWitness.routeWitness.metadata.source.periodTranslate
      formula secondSourceShift).incidenceDrawing formula).routes
        second.segmentWitness.routeWitness.metadata.source.localClauseIndex
        second.segmentWitness.taggedLiteral.2)
  let firstPoint := Cell.add firstOffset first.physicalPoint
  let secondPoint := Cell.add secondOffset second.physicalPoint
  have firstPointMember :
      (firstPoint, firstIndexed.pointIndex) ∈ firstRoute.zipIdx := by
    simpa only [firstPoint, firstRoute, firstOffset] using
      first.physicalPoint_periodTranslate_mem_sourceRoute
        firstSourceShift
  have secondPointMember :
      (secondPoint, secondIndexed.pointIndex) ∈ secondRoute.zipIdx := by
    simpa only [secondPoint, secondRoute, secondOffset] using
      second.physicalPoint_periodTranslate_mem_sourceRoute
        secondSourceShift
  have liftedPhysicalPointEq :
      Cell.add first.physicalPoint
          (placement.translation first.segmentWitness.physicalShift) =
        Cell.add second.physicalPoint
          (placement.translation second.segmentWitness.physicalShift) :=
    first.pointEq.symm.trans (equal.trans second.pointEq)
  have firstOffsetEq :
      firstOffset = placement.translation firstSourceShift :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula firstSourceShift).symm
  have secondOffsetEq :
      secondOffset = placement.translation secondSourceShift :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula secondSourceShift).symm
  have firstAlignedEq :
      Cell.add firstPoint
          (placement.translation
            (Cell.sub first.segmentWitness.physicalShift firstSourceShift)) =
        Cell.add first.physicalPoint
          (placement.translation first.segmentWitness.physicalShift) := by
    dsimp only [firstPoint]
    rw [firstOffsetEq]
    simpa [Cell.add, add_comm] using
      point_add_placement_add_sub placement first.physicalPoint
        first.segmentWitness.physicalShift firstSourceShift
  have secondAlignedEq :
      Cell.add secondPoint
          (placement.translation
            (Cell.sub second.segmentWitness.physicalShift secondSourceShift)) =
        Cell.add second.physicalPoint
          (placement.translation second.segmentWitness.physicalShift) := by
    dsimp only [secondPoint]
    rw [secondOffsetEq]
    simpa [Cell.add, add_comm] using
      point_add_placement_add_sub placement second.physicalPoint
        second.segmentWitness.physicalShift secondSourceShift
  have translatedPointEq :
      Cell.add firstPoint
          (placement.translation
            (Cell.sub first.segmentWitness.physicalShift firstSourceShift)) =
        Cell.add secondPoint
          (placement.translation
            (Cell.sub first.segmentWitness.physicalShift firstSourceShift)) := by
    rw [firstAlignedEq, commonShiftEq, secondAlignedEq]
    exact liftedPhysicalPointEq
  have pointEq : firstPoint = secondPoint := by
    apply
      Cell.add_left_injective
        (placement.translation
          (Cell.sub first.segmentWitness.physicalShift firstSourceShift))
    simpa [Cell.add, add_comm] using translatedPointEq
  have firstPointIndexLt :
      firstIndexed.pointIndex < firstRoute.length :=
    List.snd_lt_of_mem_zipIdx firstPointMember
  have secondPointIndexLt :
      secondIndexed.pointIndex < secondRoute.length :=
    List.snd_lt_of_mem_zipIdx secondPointMember
  let firstPointIndex : Fin firstRoute.length :=
    ⟨firstIndexed.pointIndex, firstPointIndexLt⟩
  let secondPointIndex : Fin secondRoute.length :=
    ⟨secondIndexed.pointIndex, secondPointIndexLt⟩
  have firstPointAt :
      firstRoute.get firstPointIndex = firstPoint :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp firstPointMember)).2
  have secondPointAt :
      secondRoute.get secondPointIndex = secondPoint :=
    (List.getElem?_eq_some_iff.mp
      ((List.mem_zipIdx_iff_getElem?).mp secondPointMember)).2
  have endpoints :
      EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          firstRoute (firstRoute.get firstPointIndex) ∧
        EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          secondRoute (secondRoute.get secondPointIndex) := by
    apply routeAvoid.2.2.2 firstPointIndex secondPointIndex
    rw [firstPointAt, secondPointAt]
    exact pointEq
  have endpointPoints :
      EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          firstRoute firstPoint ∧
        EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
          secondRoute secondPoint := by
    rw [firstPointAt, secondPointAt] at endpoints
    exact endpoints
  have firstSimple :
      LocalIncidenceDrawing.RouteIsSimple firstRoute := by
    have physicalSimple :=
      first.physicalRoute_isSimple
        formula wellFormed degree isLocal clausesNonempty
    dsimp only [firstRoute]
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    exact
      EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        physicalSimple firstOffset
  have secondSimple :
      LocalIncidenceDrawing.RouteIsSimple secondRoute := by
    have physicalSimple :=
      second.physicalRoute_isSimple
        formula wellFormed degree isLocal clausesNonempty
    dsimp only [secondRoute]
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    exact
      EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
        physicalSimple secondOffset
  have firstEndpoint :=
    EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
      firstSimple.1 firstPointMember endpointPoints.1
  have secondEndpoint :=
    EmbeddedCNFIncidenceDrawing.indexedRoutePoint_isEndpoint_of_routePointIsEndpoint
      secondSimple.1 secondPointMember endpointPoints.2
  have firstRouteLengthEq :
      firstRoute.length = firstIndexed.routeLength := by
    have physicalLengthEq :
        ((first.segmentWitness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            first.segmentWitness.routeWitness.metadata.source.localClauseIndex
            first.segmentWitness.taggedLiteral.2).length =
          firstIndexed.routeLength := by
      simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
        retainedDrawingPlanarSATLocalIncidenceRoutes,
        metadataPhysicalIncidence,
        EmbeddedCNFIncidenceDrawing.routeAt,
        first.segmentWitness.routeWitness.metadataLookup] using
          first.physicalRouteLengthEq
    dsimp only [firstRoute]
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    simpa [translatePolyline] using physicalLengthEq
  have secondRouteLengthEq :
      secondRoute.length = secondIndexed.routeLength := by
    have physicalLengthEq :
        ((second.segmentWitness.routeWitness.metadata.source.incidenceDrawing
          formula).routes
            second.segmentWitness.routeWitness.metadata.source.localClauseIndex
            second.segmentWitness.taggedLiteral.2).length =
          secondIndexed.routeLength := by
      simpa [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
        retainedDrawingPlanarSATLocalIncidenceRoutes,
        metadataPhysicalIncidence,
        EmbeddedCNFIncidenceDrawing.routeAt,
        second.segmentWitness.routeWitness.metadataLookup] using
          second.physicalRouteLengthEq
    dsimp only [secondRoute]
    rw [
      DrawingPlanarSATClauseSource.incidenceDrawing_routes_periodTranslate]
    simpa [translatePolyline] using physicalLengthEq
  constructor
  · simpa only [IndexedRoutePoint.IsEndpoint, firstRouteLengthEq] using
      firstEndpoint
  · simpa only [IndexedRoutePoint.IsEndpoint, secondRouteLengthEq] using
      secondEndpoint

end PeriodicOrthocrossing
end LeanTrominoes
