import LeanTrominoes.PositionedPeriodicCNFRebasedRouteBounds

/-!
# Endpoint-only contacts in periodic grid drawings

Continuous separation of segment interiors does not by itself make a
polyline drawing a topological embedding: two unrelated routes could still
pass through the same listed bend point.  Before replacing one route by a
positive-width ribbon, we therefore also require distinct lifted route-point
occurrences to meet only when both are outer endpoints of their routes.

For routes whose points lie in the open one-cell halo, equality again bounds
the relative period translation to the `5 × 5` double-neighbor window.  The
global condition consequently has an executable finite checker.
-/

namespace LeanTrominoes

/-- A listed polyline point together with its syntactic route and point
indices.  The route length makes the outer-endpoint test independent of
searching for an equal point elsewhere in the route. -/
structure IndexedRoutePoint where
  routeIndex : Nat
  pointIndex : Nat
  routeLength : Nat
  point : Cell
  deriving DecidableEq, Repr

namespace IndexedRoutePoint

/-- The indexed point is the first or last listed point of its route. -/
def IsEndpoint (indexed : IndexedRoutePoint) : Prop :=
  indexed.pointIndex = 0 ∨
    indexed.pointIndex + 1 = indexed.routeLength

instance (indexed : IndexedRoutePoint) :
    Decidable indexed.IsEndpoint := by
  unfold IsEndpoint
  infer_instance

end IndexedRoutePoint

namespace PeriodicGridDrawing

/-- Every listed route-point occurrence in presentation order. -/
def indexedRoutePoints (drawing : PeriodicGridDrawing) :
    List IndexedRoutePoint :=
  drawing.edgeRoutes.zipIdx.flatMap fun taggedRoute =>
    taggedRoute.1.zipIdx.map fun taggedPoint =>
      { routeIndex := taggedRoute.2
        pointIndex := taggedPoint.2
        routeLength := taggedRoute.1.length
        point := taggedPoint.1 }

/-- Identity of one listed route point in the infinite periodic lift. -/
def RoutePointOccurrenceKey
    (indexed : IndexedRoutePoint) (translate : Cell) :
    Nat × Nat × Cell :=
  (indexed.routeIndex, indexed.pointIndex, translate)

/-- Distinct lifted listed points may coincide only at outer route
endpoints.  In particular, unrelated bends cannot hide a topological
crossing that segment-interior predicates fail to see. -/
def RoutePointsMeetOnlyAtEndpoints
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedRoutePoints,
    ∀ second ∈ drawing.indexedRoutePoints,
      ∀ firstTranslate secondTranslate,
        RoutePointOccurrenceKey first firstTranslate ≠
            RoutePointOccurrenceKey second secondTranslate →
          Cell.add first.point
              (drawing.periodTranslation firstTranslate) =
            Cell.add second.point
              (drawing.periodTranslation secondTranslate) →
          first.IsEndpoint ∧ second.IsEndpoint

/-- Pointwise halo bounds transfer directly to the indexed point
enumeration. -/
theorem indexedRoutePoint_inside_expanded
    {drawing : PeriodicGridDrawing}
    (bounds : drawing.RoutePointsInExpandedSquare)
    {indexed : IndexedRoutePoint}
    (member : indexed ∈ drawing.indexedRoutePoints) :
    drawing.PositionInExpandedSquare indexed.point := by
  unfold indexedRoutePoints at member
  rcases List.mem_flatMap.mp member with
    ⟨taggedRoute, taggedRouteMember, indexedMember⟩
  rcases List.mem_map.mp indexedMember with
    ⟨taggedPoint, taggedPointMember, indexedEqual⟩
  subst indexed
  apply bounds taggedRoute.1
  · exact List.fst_mem_of_mem_zipIdx taggedRouteMember
  · exact List.fst_mem_of_mem_zipIdx taggedPointMember

/-- Equality of two halo-bounded lifted route points limits their relative
period translation to the double-neighbor window. -/
theorem relativeTranslate_isDoubleNeighbor_of_routePoint_eq
    {drawing : PeriodicGridDrawing}
    (bounds : drawing.RoutePointsInExpandedSquare)
    {first second : IndexedRoutePoint}
    (firstMember : first ∈ drawing.indexedRoutePoints)
    (secondMember : second ∈ drawing.indexedRoutePoints)
    {firstTranslate secondTranslate : Cell}
    (equal :
      Cell.add first.point
          (drawing.periodTranslation firstTranslate) =
        Cell.add second.point
          (drawing.periodTranslation secondTranslate)) :
    Cell.sub firstTranslate secondTranslate ∈
      doubleNeighborTranslations := by
  have firstBounds :=
    indexedRoutePoint_inside_expanded bounds firstMember
  have secondBounds :=
    indexedRoutePoint_inside_expanded bounds secondMember
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  apply
    (mem_doubleNeighborTranslations_iff
      (Cell.sub firstTranslate secondTranslate)).mpr
  rcases first with ⟨firstRoute, firstIndex, firstLength,
    ⟨firstX, firstY⟩⟩
  rcases second with ⟨secondRoute, secondIndex, secondLength,
    ⟨secondX, secondY⟩⟩
  rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
  rcases secondTranslate with ⟨secondTranslateX, secondTranslateY⟩
  simp only [PositionInExpandedSquare] at firstBounds secondBounds
  simp only [Cell.add, periodTranslation, Cell.scale,
    Prod.mk.injEq] at equal
  simp only [Cell.sub]
  have horizontalEqual :
      secondX =
        firstX +
          drawing.gridSize *
            (firstTranslateX - secondTranslateX) := by
    calc
      secondX =
          firstX +
            drawing.gridSize * firstTranslateX -
              drawing.gridSize * secondTranslateX := by omega
      _ =
          firstX +
            drawing.gridSize *
              (firstTranslateX - secondTranslateX) := by ring
  have verticalEqual :
      secondY =
        firstY +
          drawing.gridSize *
            (firstTranslateY - secondTranslateY) := by
    calc
      secondY =
          firstY +
            drawing.gridSize * firstTranslateY -
              drawing.gridSize * secondTranslateY := by omega
      _ =
          firstY +
            drawing.gridSize *
              (firstTranslateY - secondTranslateY) := by ring
  constructor
  · exact lane_shift_is_doubleNeighbor periodPositive
      firstBounds.1 firstBounds.2.1
      secondBounds.1 secondBounds.2.1 horizontalEqual
  · exact lane_shift_is_doubleNeighbor periodPositive
      firstBounds.2.2.1 firstBounds.2.2.2
      secondBounds.2.2.1 secondBounds.2.2.2 verticalEqual

/-- Normalizing by the second translation turns a lifted point equality
into equality at one relative translation. -/
theorem routePoint_eq_normalize
    (drawing : PeriodicGridDrawing)
    (first second : IndexedRoutePoint)
    (firstTranslate secondTranslate : Cell) :
    Cell.add first.point
          (drawing.periodTranslation firstTranslate) =
        Cell.add second.point
          (drawing.periodTranslation secondTranslate) ↔
      Cell.add first.point
          (drawing.periodTranslation
            (Cell.sub firstTranslate secondTranslate)) =
        second.point := by
  rcases first.point with ⟨firstX, firstY⟩
  rcases second.point with ⟨secondX, secondY⟩
  rcases firstTranslate with ⟨firstTranslateX, firstTranslateY⟩
  rcases secondTranslate with ⟨secondTranslateX, secondTranslateY⟩
  simp only [Cell.add, periodTranslation, Cell.scale, Cell.sub,
    Prod.mk.injEq]
  constructor <;> intro equal
  · constructor <;> nlinarith [equal.1, equal.2]
  · constructor <;> nlinarith [equal.1, equal.2]

/-- A globally distinct pair stays distinct after replacing its two
translations by their relative translation and zero. -/
theorem relative_routePoint_key_ne
    {first second : IndexedRoutePoint}
    {firstTranslate secondTranslate : Cell}
    (different :
      RoutePointOccurrenceKey first firstTranslate ≠
        RoutePointOccurrenceKey second secondTranslate) :
    RoutePointOccurrenceKey first
        (Cell.sub firstTranslate secondTranslate) ≠
      RoutePointOccurrenceKey second (0, 0) := by
  intro equal
  apply different
  simp only [RoutePointOccurrenceKey] at equal ⊢
  rcases firstTranslate with ⟨firstX, firstY⟩
  rcases secondTranslate with ⟨secondX, secondY⟩
  simp only [Cell.sub, Prod.mk.injEq] at equal ⊢
  omega

/-- Exact endpoint-contact check over all halo-relevant relative
translations. -/
def expandedFiniteRoutePointsMeetOnlyAtEndpoints
    (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedRoutePoints.all fun first =>
    drawing.indexedRoutePoints.all fun second =>
      doubleNeighborTranslations.all fun relative =>
        decide
          (RoutePointOccurrenceKey first relative =
              RoutePointOccurrenceKey second (0, 0) ∨
            Cell.add first.point
                (drawing.periodTranslation relative) ≠
              second.point ∨
            (first.IsEndpoint ∧ second.IsEndpoint))

theorem expandedFiniteRoutePointsMeetOnlyAtEndpoints_spec
    {drawing : PeriodicGridDrawing}
    (checked :
      drawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints = true) :
    ∀ first ∈ drawing.indexedRoutePoints,
      ∀ second ∈ drawing.indexedRoutePoints,
        ∀ relative ∈ doubleNeighborTranslations,
          RoutePointOccurrenceKey first relative =
              RoutePointOccurrenceKey second (0, 0) ∨
            Cell.add first.point
                (drawing.periodTranslation relative) ≠
              second.point ∨
            (first.IsEndpoint ∧ second.IsEndpoint) := by
  simpa [expandedFiniteRoutePointsMeetOnlyAtEndpoints] using checked

/-- The finite endpoint-contact check proves the corresponding condition
for the complete infinite periodic lift. -/
theorem routePointsMeetOnlyAtEndpoints_of_expandedFinite
    {drawing : PeriodicGridDrawing}
    (bounds : drawing.RoutePointsInExpandedSquare)
    (checked :
      drawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints = true) :
    drawing.RoutePointsMeetOnlyAtEndpoints := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate different equal
  let relative := Cell.sub firstTranslate secondTranslate
  have relativeMember :=
    relativeTranslate_isDoubleNeighbor_of_routePoint_eq bounds
      firstMember secondMember equal
  have normalized :
      Cell.add first.point
          (drawing.periodTranslation relative) =
        second.point :=
    (routePoint_eq_normalize drawing first second
      firstTranslate secondTranslate).mp equal
  rcases
      expandedFiniteRoutePointsMeetOnlyAtEndpoints_spec checked
        first firstMember second secondMember
        relative relativeMember with same | unequal | endpoints
  · exact (relative_routePoint_key_ne different same).elim
  · exact (unequal normalized).elim
  · exact endpoints

/-- Continuous planarity together with endpoint-only listed-point contacts
is the source geometry needed for topological ribbon thickening. -/
def IsRibbonReady (drawing : PeriodicGridDrawing) : Prop :=
  drawing.IsContinuouslyPlanar ∧
    drawing.RoutePointsMeetOnlyAtEndpoints

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- A continuously planar, halo-bounded incidence presentation with no
listed-point contacts except at advertised route endpoints.  This is the
source interface consumed by the ribbon construction. -/
structure HaloBoundedRibbonReadyIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    extends
      HaloBoundedContinuousPlanarIncidencePresentation source placement
    where
  endpointContacts :
    (incidenceDrawing source placement routes)
      |>.RoutePointsMeetOnlyAtEndpoints

namespace HaloBoundedRibbonReadyIncidencePresentation

/-- Anchor normalization changes none of the finite drawing data and
therefore preserves endpoint-only route-point contacts. -/
def anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      HaloBoundedRibbonReadyIncidencePresentation source placement) :
    HaloBoundedRibbonReadyIncidencePresentation
      (source.anchorNormalize placement) placement where
  toHaloBoundedContinuousPlanarIncidencePresentation :=
    presentation.toHaloBoundedContinuousPlanarIncidencePresentation
      |>.anchorNormalize
  endpointContacts := by
    rw [incidenceDrawing_anchorNormalize]
    exact presentation.endpointContacts

end HaloBoundedRibbonReadyIncidencePresentation
end PositionedPeriodicCNF
end LeanTrominoes
