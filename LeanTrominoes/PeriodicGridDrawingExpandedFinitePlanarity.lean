import LeanTrominoes.PeriodicGridDrawingExpandedBounds

/-!
# Finite planarity checking for halo-bounded periodic routes

For route endpoints in the open one-cell halo, route/route contacts reduce
to the 25 relative translations in `doubleNeighborTranslations`.  Stored
vertices still lie in the canonical fundamental square, so vertex/route
contacts continue to use the original nine-neighbor check.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

open PeriodicOrthocrossing

/-- Boolean route-interior check over all 25 relative translations allowed
by halo-bounded endpoints. -/
def expandedFiniteRoutesAvoidInteriors
    (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun first =>
    drawing.indexedSegments.all fun second =>
      doubleNeighborTranslations.all fun relative =>
        (segmentInteriorPoints
          (first.segment.translate
            (drawing.periodTranslation relative))).all fun point =>
          decide
            (SegmentOccurrenceKey first relative =
                SegmentOccurrenceKey second (0, 0) ∨
              ¬second.segment.Contains point)

theorem expandedFiniteRoutesAvoidInteriors_spec
    {drawing : PeriodicGridDrawing}
    (checked :
      drawing.expandedFiniteRoutesAvoidInteriors = true) :
    ∀ first ∈ drawing.indexedSegments,
      ∀ second ∈ drawing.indexedSegments,
        ∀ relative ∈ doubleNeighborTranslations,
          ∀ point,
            (first.segment.translate
              (drawing.periodTranslation relative)).InteriorContains
                point →
            SegmentOccurrenceKey first relative =
                SegmentOccurrenceKey second (0, 0) ∨
              ¬second.segment.Contains point := by
  intro first firstMember second secondMember
    relative relativeMember point contains
  have raw := checked
  simp only [expandedFiniteRoutesAvoidInteriors,
    List.all_eq_true] at raw
  exact of_decide_eq_true
    (raw first firstMember second secondMember
      relative relativeMember point
      ((mem_segmentInteriorPoints_iff _ _).mpr contains))

/-- The 25-translation finite check proves global route-interior avoidance
for halo-bounded stored routes. -/
theorem routesAvoidInteriors_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    (checked :
      drawing.expandedFiniteRoutesAvoidInteriors = true) :
    drawing.RoutesAvoidInteriors := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate point different
    firstContains secondContains
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have relativeMember :=
    relativeTranslate_isDoubleNeighbor_of_contact
      endpointBounds firstMember secondMember
      firstContains secondContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  rcases expandedFiniteRoutesAvoidInteriors_spec checked
      first firstMember second secondMember
      relative relativeMember normalized normalizedFirst with
    same | avoids
  · exact (relative_key_ne different same).elim
  · exact (avoids normalizedSecond).elim

/-- A halo-bounded route occurrence meeting a stored fundamental-square
vertex uses one of the original nine neighboring translations. -/
theorem relativeTranslate_isNeighbor_of_expandedVertexContact
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    {vertex : Cell}
    (vertexBounds : drawing.PositionInFundamentalSquare vertex)
    {indexed : IndexedGridSegment}
    (indexedMember : indexed ∈ drawing.indexedSegments)
    {vertexTranslate routeTranslate : Cell}
    (contains :
      (indexed.segment.translate
        (drawing.periodTranslation routeTranslate)).InteriorContains
        (Cell.add vertex
          (drawing.periodTranslation vertexTranslate))) :
    Cell.sub routeTranslate vertexTranslate ∈
      neighborTranslations := by
  let relative := Cell.sub routeTranslate vertexTranslate
  have normalized :
      (indexed.segment.translate
        (drawing.periodTranslation relative)).InteriorContains vertex := by
    have := (interiorContains_normalize drawing indexed.segment
      routeTranslate vertexTranslate
      (Cell.add vertex
        (drawing.periodTranslation vertexTranslate))).mp contains
    simpa [relative, normalizePoint, Cell.add, Cell.sub] using this
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have segmentBounds := endpointBounds indexed indexedMember
  apply (mem_neighborTranslations_iff relative).mpr
  rcases segmentBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases vertexBounds with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases normalized with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · have same' :
        vertex.2 =
          indexed.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.1 +
            drawing.gridSize * relative.1)
          (indexed.segment.finish.1 +
            drawing.gridSize * relative.1)
          vertex.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_shift_is_neighbor periodPositive
          startXLower startXUpper finishXLower finishXUpper
          (by omega) (by omega) between',
        lane_shift_is_neighbor periodPositive
          startYLower startYUpper
          (by omega) (by omega) same'⟩
  · have same' :
        vertex.1 =
          indexed.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.2 +
            drawing.gridSize * relative.2)
          (indexed.segment.finish.2 +
            drawing.gridSize * relative.2)
          vertex.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨lane_shift_is_neighbor periodPositive
          startXLower startXUpper
          (by omega) (by omega) same',
        between_shift_is_neighbor periodPositive
          startYLower startYUpper finishYLower finishYUpper
          (by omega) (by omega) between'⟩

/-- The existing nine-translation Boolean vertex check remains complete
under halo endpoint bounds. -/
theorem verticesAvoidRouteInteriors_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (checked :
      drawing.finiteVerticesAvoidRouteInteriors = true) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertex vertexMember indexed indexedMember
    vertexTranslate routeTranslate contains
  let relative := Cell.sub routeTranslate vertexTranslate
  have relativeMember :=
    relativeTranslate_isNeighbor_of_expandedVertexContact
      endpointBounds (vertexBounds vertex vertexMember)
      indexedMember contains
  have normalized :
      (indexed.segment.translate
        (drawing.periodTranslation relative)).InteriorContains vertex := by
    have := (interiorContains_normalize drawing indexed.segment
      routeTranslate vertexTranslate
      (Cell.add vertex
        (drawing.periodTranslation vertexTranslate))).mp contains
    simpa [relative, normalizePoint, Cell.add, Cell.sub] using this
  exact
    finiteVerticesAvoidRouteInteriors_spec checked
      vertex vertexMember indexed indexedMember
      relative relativeMember normalized

/-- The expanded route check and the existing vertex check certify global
periodic planarity for halo-bounded routes. -/
theorem isPlanar_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (endpointBounds :
      drawing.SegmentEndpointsInExpandedSquare)
    (vertexBounds :
      ∀ vertex ∈ drawing.vertexPositions,
        drawing.PositionInFundamentalSquare vertex)
    (routesChecked :
      drawing.expandedFiniteRoutesAvoidInteriors = true)
    (verticesChecked :
      drawing.finiteVerticesAvoidRouteInteriors = true) :
    drawing.IsPlanar :=
  ⟨routesAvoidInteriors_of_expandedFinite
      endpointBounds routesChecked,
    verticesAvoidRouteInteriors_of_expandedFinite
      endpointBounds vertexBounds verticesChecked⟩

end PeriodicGridDrawing
end LeanTrominoes
