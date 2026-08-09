import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDrawing

/-!
# Continuous route separation under variable gauges

A variable gauge changes canonical representatives but not the infinite
periodic route arrangement.  Every stored route is translated by a whole
period, so segment occurrences are carried bijectively to occurrences of
the ungauged drawing.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

set_option maxHeartbeats 800000

private theorem tagged_eq_of_mem_zipIdx_of_snd_eq
    {Item : Type*} {items : List Item}
    {first second : Item × Nat}
    (firstMember : first ∈ items.zipIdx)
    (secondMember : second ∈ items.zipIdx)
    (indicesEqual : first.2 = second.2) :
    first = second := by
  apply Prod.ext
  · have firstAt := (List.mem_zipIdx_iff_getElem?).mp firstMember
    have secondAt := (List.mem_zipIdx_iff_getElem?).mp secondMember
    rw [indicesEqual, secondAt] at firstAt
    exact Option.some.inj firstAt.symm
  · exact indicesEqual

private theorem periodTranslation_add
    (drawing : PeriodicGridDrawing) (first second : Cell) :
    drawing.periodTranslation (Cell.add first second) =
      Cell.add (drawing.periodTranslation first)
        (drawing.periodTranslation second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.add]
  constructor <;> ring

private theorem gridSegment_translate_translate
    (segment : GridSegment) (first second : Cell) :
    (segment.translate first).translate second =
      segment.translate (Cell.add first second) := by
  rcases segment with ⟨start, finish⟩
  rcases start with ⟨startX, startY⟩
  rcases finish with ⟨finishX, finishY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [GridSegment.translate, Cell.add]
  constructor <;> constructor <;> ring

/-- Translating every canonical incidence route by the whole-period shift
induced by a variable gauge preserves global continuous segment
separation. -/
theorem incidenceDrawing_variableGaugeCanonicalIncidenceRoutes_routesHaveDisjointInteriors
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (gauge : Variable → Cell)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (continuous :
      (incidenceDrawing source placement routes).IsContinuouslyPlanar) :
    (incidenceDrawing
      (source.variableGauge gauge)
      (placement.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).RoutesHaveDisjointInteriors := by
  let sourceDrawing := incidenceDrawing source placement routes
  let targetDrawing := incidenceDrawing
    (source.variableGauge gauge)
    (placement.variableGauge gauge)
    (variableGaugeCanonicalIncidenceRoutes source placement gauge routes)
  intro first firstMember second secondMember
    firstTranslate secondTranslate keysDifferent
  unfold PeriodicGridDrawing.indexedSegments at firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstRoute, firstRouteMember, firstSegmentMember⟩
  rcases List.mem_map.mp firstSegmentMember with
    ⟨firstSegment, firstSegmentMember, firstIndexedEqual⟩
  have firstSegmentTaggedMember :
      firstSegment ∈ (gridPolylineSegments firstRoute.1).zipIdx :=
    firstSegmentMember
  subst first
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondRoute, secondRouteMember, secondSegmentMember⟩
  rcases List.mem_map.mp secondSegmentMember with
    ⟨secondSegment, secondSegmentMember, secondIndexedEqual⟩
  have secondSegmentTaggedMember :
      secondSegment ∈ (gridPolylineSegments secondRoute.1).zipIdx :=
    secondSegmentMember
  subst second
  change firstRoute ∈
    (incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).zipIdx at firstRouteMember
  change secondRoute ∈
    (incidenceEdgeRoutes
      (source.variableGauge gauge)
      (variableGaugeCanonicalIncidenceRoutes
        source placement gauge routes)).zipIdx at secondRouteMember
  rw [incidenceEdgeRoutes_eq_metadata_map,
    erase_variableGauge,
    PeriodicCNF.incidencesWithMetadata_variableGauge,
    List.map_map, List.zipIdx_map] at firstRouteMember secondRouteMember
  rcases List.mem_map.mp firstRouteMember with
    ⟨firstTaggedIncidence, firstTaggedIncidenceMember,
      firstRouteTaggedEqual⟩
  rcases List.mem_map.mp secondRouteMember with
    ⟨secondTaggedIncidence, secondTaggedIncidenceMember,
      secondRouteTaggedEqual⟩
  rcases incidenceMetadata_of_tagged source
      firstTaggedIncidenceMember with
    ⟨firstClause, firstLiteral, firstClauseMember,
      firstLiteralMember, firstIncidenceEqual⟩
  rcases incidenceMetadata_of_tagged source
      secondTaggedIncidenceMember with
    ⟨secondClause, secondLiteral, secondClauseMember,
      secondLiteralMember, secondIncidenceEqual⟩
  let firstShift := variableGaugeCanonicalRouteShift gauge firstClause
  let secondShift := variableGaugeCanonicalRouteShift gauge secondClause
  have firstRouteValueEqual :
      firstRoute.1 =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation firstShift)
          (routes firstTaggedIncidence.1.clauseIndex
            firstTaggedIncidence.1.literalIndex) := by
    have routeEqual :=
      variableGaugeCanonicalIncidenceRoutes_of_clause_mem
        source placement gauge routes firstClauseMember
        (literalIndex := firstTaggedIncidence.1.literalIndex)
    have taggedValueEqual := congrArg Prod.fst firstRouteTaggedEqual
    simpa [firstShift] using taggedValueEqual.symm.trans routeEqual
  have firstRouteIndexEqual :
      firstRoute.2 = firstTaggedIncidence.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd firstRouteTaggedEqual).symm
  have secondRouteValueEqual :
      secondRoute.1 =
        PeriodicOrthocrossing.translatePolyline
          (placement.translation secondShift)
          (routes secondTaggedIncidence.1.clauseIndex
            secondTaggedIncidence.1.literalIndex) := by
    have routeEqual :=
      variableGaugeCanonicalIncidenceRoutes_of_clause_mem
        source placement gauge routes secondClauseMember
        (literalIndex := secondTaggedIncidence.1.literalIndex)
    have taggedValueEqual := congrArg Prod.fst secondRouteTaggedEqual
    simpa [secondShift] using taggedValueEqual.symm.trans routeEqual
  have secondRouteIndexEqual :
      secondRoute.2 = secondTaggedIncidence.2 := by
    simpa only [Prod.map, id_eq] using
      (congrArg Prod.snd secondRouteTaggedEqual).symm
  rw [firstRouteValueEqual,
    PeriodicOrthocrossing.translatePolyline,
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
    List.zipIdx_map] at firstSegmentTaggedMember
  rcases List.mem_map.mp firstSegmentTaggedMember with
    ⟨firstSourceSegment, firstSourceSegmentMember,
      firstSegmentTaggedEqual⟩
  rw [secondRouteValueEqual,
    PeriodicOrthocrossing.translatePolyline,
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_map_add,
    List.zipIdx_map] at secondSegmentTaggedMember
  rcases List.mem_map.mp secondSegmentTaggedMember with
    ⟨secondSourceSegment, secondSourceSegmentMember,
      secondSegmentTaggedEqual⟩
  let firstSourceIndexed : IndexedGridSegment :=
    ⟨firstTaggedIncidence.2, firstSourceSegment.2,
      firstSourceSegment.1⟩
  let secondSourceIndexed : IndexedGridSegment :=
    ⟨secondTaggedIncidence.2, secondSourceSegment.2,
      secondSourceSegment.1⟩
  have firstSourceRouteMember :
      (routes firstTaggedIncidence.1.clauseIndex
          firstTaggedIncidence.1.literalIndex,
        firstTaggedIncidence.2) ∈ sourceDrawing.edgeRoutes.zipIdx := by
    exact taggedRoute_mem_of_taggedIncidence
      source placement routes firstTaggedIncidenceMember
  have secondSourceRouteMember :
      (routes secondTaggedIncidence.1.clauseIndex
          secondTaggedIncidence.1.literalIndex,
        secondTaggedIncidence.2) ∈ sourceDrawing.edgeRoutes.zipIdx := by
    exact taggedRoute_mem_of_taggedIncidence
      source placement routes secondTaggedIncidenceMember
  have firstSourceIndexedMember :
      firstSourceIndexed ∈ sourceDrawing.indexedSegments := by
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨_, firstSourceRouteMember, ?_⟩
    exact List.mem_map.mpr
      ⟨firstSourceSegment, firstSourceSegmentMember, rfl⟩
  have secondSourceIndexedMember :
      secondSourceIndexed ∈ sourceDrawing.indexedSegments := by
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨_, secondSourceRouteMember, ?_⟩
    exact List.mem_map.mpr
      ⟨secondSourceSegment, secondSourceSegmentMember, rfl⟩
  have sourceKeysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey firstSourceIndexed
          (Cell.add firstShift firstTranslate) ≠
        PeriodicGridDrawing.SegmentOccurrenceKey secondSourceIndexed
          (Cell.add secondShift secondTranslate) := by
    intro sourceKeysEqual
    apply keysDifferent
    simp only [PeriodicGridDrawing.SegmentOccurrenceKey,
      Prod.mk.injEq] at sourceKeysEqual ⊢
    rcases sourceKeysEqual with
      ⟨routeIndicesEqual, segmentIndicesEqual, translatedEqual⟩
    have taggedIncidencesEqual :
        firstTaggedIncidence = secondTaggedIncidence :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        firstTaggedIncidenceMember secondTaggedIncidenceMember
        routeIndicesEqual
    subst secondTaggedIncidence
    have clausesEqual : firstClause = secondClause := by
      have taggedClausesEqual :
          (firstClause, firstTaggedIncidence.1.clauseIndex) =
            (secondClause, firstTaggedIncidence.1.clauseIndex) :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          firstClauseMember secondClauseMember rfl
      exact congrArg Prod.fst taggedClausesEqual
    subst secondClause
    have translatesEqual : firstTranslate = secondTranslate := by
      have shiftsEqual : secondShift = firstShift := by rfl
      rw [shiftsEqual] at translatedEqual
      rcases firstShift with ⟨shiftX, shiftY⟩
      rcases firstTranslate with ⟨firstX, firstY⟩
      rcases secondTranslate with ⟨secondX, secondY⟩
      simp only [Cell.add, Prod.mk.injEq] at translatedEqual ⊢
      omega
    subst secondTranslate
    have targetSegmentIndicesEqual :
        firstSegment.2 = secondSegment.2 := by
      have firstIndexEqual :
          firstSourceSegment.2 = firstSegment.2 := by
        simpa only [Prod.map, id_eq] using
          congrArg Prod.snd firstSegmentTaggedEqual
      have secondIndexEqual :
          secondSourceSegment.2 = secondSegment.2 := by
        simpa only [Prod.map, id_eq] using
          congrArg Prod.snd secondSegmentTaggedEqual
      exact firstIndexEqual.symm.trans
        (segmentIndicesEqual.trans secondIndexEqual)
    exact ⟨firstRouteIndexEqual.trans secondRouteIndexEqual.symm,
      targetSegmentIndicesEqual, rfl⟩
  have sourceAvoid := continuous.noInteriorsMeet
    firstSourceIndexedMember secondSourceIndexedMember
    sourceKeysDifferent
  intro targetMeet
  apply sourceAvoid
  have firstShiftPhysical :
      placement.translation firstShift =
        sourceDrawing.periodTranslation firstShift := by
    simp [sourceDrawing, PeriodicVariablePlacement.translation,
      PeriodicGridDrawing.periodTranslation,
      incidenceDrawing_gridSize source placement routes periodPositive]
  have secondShiftPhysical :
      placement.translation secondShift =
        sourceDrawing.periodTranslation secondShift := by
    simp [sourceDrawing, PeriodicVariablePlacement.translation,
      PeriodicGridDrawing.periodTranslation,
      incidenceDrawing_gridSize source placement routes periodPositive]
  have firstSegmentValueEqual :
      firstSegment.1 =
        firstSourceSegment.1.translate
          (sourceDrawing.periodTranslation firstShift) := by
    have valueEqual := congrArg Prod.fst firstSegmentTaggedEqual
    simpa [firstShiftPhysical] using valueEqual.symm
  have secondSegmentValueEqual :
      secondSegment.1 =
        secondSourceSegment.1.translate
          (sourceDrawing.periodTranslation secondShift) := by
    have valueEqual := congrArg Prod.fst secondSegmentTaggedEqual
    simpa [secondShiftPhysical] using valueEqual.symm
  have targetPeriodFirst :
      targetDrawing.periodTranslation firstTranslate =
        sourceDrawing.periodTranslation firstTranslate := by
    simp [targetDrawing, sourceDrawing,
      PeriodicGridDrawing.periodTranslation,
      incidenceDrawing_gridSize source placement routes periodPositive,
      incidenceDrawing_gridSize
        (source.variableGauge gauge)
        (placement.variableGauge gauge)
        (variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes) periodPositive]
  have targetPeriodSecond :
      targetDrawing.periodTranslation secondTranslate =
        sourceDrawing.periodTranslation secondTranslate := by
    simp [targetDrawing, sourceDrawing,
      PeriodicGridDrawing.periodTranslation,
      incidenceDrawing_gridSize source placement routes periodPositive,
      incidenceDrawing_gridSize
        (source.variableGauge gauge)
        (placement.variableGauge gauge)
        (variableGaugeCanonicalIncidenceRoutes
          source placement gauge routes) periodPositive]
  change
    GridSegment.InteriorsMeet
      (firstSegment.1.translate
        (targetDrawing.periodTranslation firstTranslate))
      (secondSegment.1.translate
        (targetDrawing.periodTranslation secondTranslate)) at targetMeet
  rw [targetPeriodFirst, targetPeriodSecond] at targetMeet
  simpa [firstSourceIndexed, secondSourceIndexed,
    firstRouteIndexEqual, secondRouteIndexEqual,
    firstSegmentValueEqual, secondSegmentValueEqual,
    gridSegment_translate_translate, periodTranslation_add]
    using targetMeet

end PositionedPeriodicCNF
end LeanTrominoes
