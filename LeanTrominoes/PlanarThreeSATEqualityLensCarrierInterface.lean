import LeanTrominoes.PlanarThreeSATCornerEqualityCarrierInterface
import LeanTrominoes.PlanarThreeSATEqualityLensPlacement

/-!
# Carrier-facing bounds of equality lenses

The left and right ends of the canonical lens occupy complementary external
wedges.  After signed-axis orientation and translation, those wedges are
exactly the absolute external port regions used by the corner interface.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The two endpoint-relative external wedges occupied by a canonical
horizontal equality lens. -/
def InHorizontalEqualityLensEndpointExteriors
    (span : Int) (point : Cell) : Prop :=
  0 ≤ point.1 ∧
    (point.1 = 0 → 0 ≤ point.2) ∧
      point.1 ≤ span ∧
        (point.1 = span → point.2 ≤ 0)

instance (span : Int) (point : Cell) :
    Decidable
      (InHorizontalEqualityLensEndpointExteriors span point) := by
  unfold InHorizontalEqualityLensEndpointExteriors
  infer_instance

/-- Every route point of the canonical lens lies in both of its
endpoint-relative external wedges. -/
theorem horizontalEqualityLensDrawing_routePoints_inEndpointExteriors
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).RoutePointsSatisfy
      (InHorizontalEqualityLensEndpointExteriors span) := by
  intro incidenceIndex point pointMember
  fin_cases incidenceIndex
  all_goals
    simp only [horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensRoutes,
      equalityInstance,
      EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      List.zipIdx_cons, List.zipIdx_nil,
      List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil,
      List.get_cons_zero, List.get_cons_succ] at pointMember
  all_goals
    simp_all [horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]
  case «0» =>
    rcases pointMember with rfl | rfl <;>
      simp [InHorizontalEqualityLensEndpointExteriors] <;> omega
  case «1» =>
    rcases pointMember with rfl | rfl | rfl | rfl <;>
      simp [InHorizontalEqualityLensEndpointExteriors] <;> omega
  case «2» =>
    rcases pointMember with rfl | rfl | rfl | rfl <;>
      simp [InHorizontalEqualityLensEndpointExteriors] <;> omega
  case «3» =>
    rcases pointMember with rfl | rfl <;>
      simp [InHorizontalEqualityLensEndpointExteriors] <;> omega

/-- A canonical lens route can list its first physical endpoint only as an
advertised route endpoint. -/
theorem horizontalEqualityLensDrawing_routeContactsAt_firstEndpoint
    (span : Int) :
    (horizontalEqualityLensDrawing
      span).RouteContactsAtEndpoint (0, 0) := by
  intro incidenceIndex point pointMember pointEqual
  fin_cases incidenceIndex
  all_goals
    simp only [horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensRoutes,
      equalityInstance,
      EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      List.zipIdx_cons, List.zipIdx_nil,
      List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil,
      List.get_cons_zero, List.get_cons_succ]
      at pointMember ⊢
  all_goals
    simp_all [horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
    omega

/-- A canonical lens route can list its second physical endpoint only as an
advertised route endpoint. -/
theorem horizontalEqualityLensDrawing_routeContactsAt_secondEndpoint
    (span : Int) :
    (horizontalEqualityLensDrawing
      span).RouteContactsAtEndpoint (span, 0) := by
  intro incidenceIndex point pointMember pointEqual
  fin_cases incidenceIndex
  all_goals
    simp only [horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensRoutes,
      equalityInstance,
      EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      List.zipIdx_cons, List.zipIdx_nil,
      List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil,
      List.get_cons_zero, List.get_cons_succ]
      at pointMember ⊢
  all_goals
    simp_all [horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
    omega

/-- External compass port at the first endpoint of a lens in one signed
axis direction. -/
def AxisDirection.firstCarrierPort : AxisDirection → CornerPort
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .invalid => .east

/-- External compass port at the second endpoint of a lens in one signed
axis direction. -/
def AxisDirection.secondCarrierPort : AxisDirection → CornerPort
  | .east => .west
  | .north => .south
  | .west => .east
  | .south => .north
  | .invalid => .west

/-- Macrocell origin recovered from the first physical endpoint and its
external compass port. -/
def AxisDirection.firstCarrierMacroOrigin
    (origin : Cell) (direction : AxisDirection) : Cell :=
  Cell.sub origin
    (AxisDirection.firstCarrierPort direction).position

/-- Macrocell origin recovered from the second physical endpoint and its
external compass port. -/
def AxisDirection.secondCarrierMacroOrigin
    (origin : Cell) (direction : AxisDirection) (span : Int) : Cell :=
  Cell.sub
    (direction.placePoint origin (span, 0))
    (AxisDirection.secondCarrierPort direction).position

/-- The first carrier macrocell origin and compass-port offset reconstruct
the first physical lens endpoint. -/
theorem AxisDirection.add_firstCarrierMacroOrigin_portPosition
    (origin : Cell) (direction : AxisDirection) :
    Cell.add
        (AxisDirection.firstCarrierMacroOrigin origin direction)
        (AxisDirection.firstCarrierPort direction).position =
      origin := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    apply Prod.ext <;>
    simp [AxisDirection.firstCarrierMacroOrigin,
      AxisDirection.firstCarrierPort,
      CornerPort.position, Cell.add, Cell.sub] <;>
    ring

/-- The second carrier macrocell origin and compass-port offset reconstruct
the second physical lens endpoint. -/
theorem AxisDirection.add_secondCarrierMacroOrigin_portPosition
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    Cell.add
        (AxisDirection.secondCarrierMacroOrigin
          origin direction span)
        (AxisDirection.secondCarrierPort direction).position =
      direction.placePoint origin (span, 0) := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    apply Prod.ext <;>
    simp [AxisDirection.secondCarrierMacroOrigin,
      AxisDirection.secondCarrierPort,
      CornerPort.position, AxisDirection.placePoint,
      AxisDirection.orientPoint, Cell.add, Cell.sub] <;>
    ring

/-- Signed-axis placement sends the canonical first-end wedge to the
absolute external region of the first compass port. -/
theorem AxisDirection.firstCarrierPort_outside_placePoint
    (origin : Cell) (direction : AxisDirection)
    {point : Cell}
    (bounded :
      0 ≤ point.1 ∧ (point.1 = 0 → 0 ≤ point.2)) :
    (AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
      (AxisDirection.firstCarrierMacroOrigin origin direction)
      (direction.placePoint origin point) := by
  rcases origin with ⟨originX, originY⟩
  rcases point with ⟨pointX, pointY⟩
  cases direction <;>
    simp [InHorizontalEqualityLensEndpointExteriors,
      AxisDirection.firstCarrierPort,
      AxisDirection.firstCarrierMacroOrigin,
      CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.position, AxisDirection.placePoint,
      AxisDirection.orientPoint, Cell.add, Cell.sub]
      at bounded ⊢ <;>
    omega

/-- Signed-axis placement sends the canonical second-end wedge to the
absolute external region of the second compass port. -/
theorem AxisDirection.secondCarrierPort_outside_placePoint
    (origin : Cell) (direction : AxisDirection)
    (span : Int) {point : Cell}
    (bounded :
      point.1 ≤ span ∧
        (point.1 = span → point.2 ≤ 0)) :
    (AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
      (AxisDirection.secondCarrierMacroOrigin origin direction span)
      (direction.placePoint origin point) := by
  rcases origin with ⟨originX, originY⟩
  rcases point with ⟨pointX, pointY⟩
  cases direction <;>
    simp [AxisDirection.secondCarrierPort,
      AxisDirection.secondCarrierMacroOrigin,
      CornerPort.OutsideCarrierBoundaryAt,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.position, AxisDirection.placePoint,
      AxisDirection.orientPoint, Cell.add, Cell.sub] at bounded ⊢ <;>
    omega

/-- Every route point of an oriented and translated lens lies on the
external side of both endpoint macrocells. -/
theorem axisEqualityLensDrawing_routePoints_outsideCarrierBoundaries
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (axisEqualityLensDrawing origin direction span).RoutePointsSatisfy
      fun point =>
        (AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
            (AxisDirection.firstCarrierMacroOrigin
              origin direction) point ∧
          (AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
            (AxisDirection.secondCarrierMacroOrigin
              origin direction span) point := by
  have canonical :=
    horizontalEqualityLensDrawing_routePoints_inEndpointExteriors
      span spanLarge
  have oriented :
      ((horizontalEqualityLensDrawing span).orient direction).RoutePointsSatisfy
        (fun point =>
          (AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
                (AxisDirection.firstCarrierMacroOrigin
                  (0, 0) direction) point ∧
            (AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
                (AxisDirection.secondCarrierMacroOrigin
                  (0, 0) direction span) point) :=
    canonical.mapPoints direction.orientPoint
      (fun point bounded =>
        ⟨by
            simpa [AxisDirection.placePoint, Cell.add] using
              AxisDirection.firstCarrierPort_outside_placePoint
                (0, 0) direction
                ⟨bounded.1, bounded.2.1⟩,
          by
            simpa [AxisDirection.placePoint, Cell.add] using
              AxisDirection.secondCarrierPort_outside_placePoint
                (0, 0) direction span
                ⟨bounded.2.2.1, bounded.2.2.2⟩⟩)
  change
    (((horizontalEqualityLensDrawing span).orient direction).translate
      origin).RoutePointsSatisfy _
  refine oriented.translate
    (targetPredicate := fun point =>
      (AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
          (AxisDirection.firstCarrierMacroOrigin
            origin direction) point ∧
        (AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span) point)
    origin ?_
  intro point bounded
  have firstOrigin :
      AxisDirection.firstCarrierMacroOrigin origin direction =
        Cell.add origin
          (AxisDirection.firstCarrierMacroOrigin
            (0, 0) direction) := by
    rcases origin with ⟨originX, originY⟩
    cases direction
    all_goals
      apply Prod.ext <;>
        simp [AxisDirection.firstCarrierMacroOrigin,
          AxisDirection.firstCarrierPort,
          CornerPort.position, Cell.add, Cell.sub] <;>
        ring
  have secondOrigin :
      AxisDirection.secondCarrierMacroOrigin origin direction span =
        Cell.add origin
          (AxisDirection.secondCarrierMacroOrigin
            (0, 0) direction span) := by
    rcases origin with ⟨originX, originY⟩
    cases direction
    all_goals
      apply Prod.ext <;>
        simp [AxisDirection.secondCarrierMacroOrigin,
          AxisDirection.secondCarrierPort,
          CornerPort.position, AxisDirection.placePoint,
          AxisDirection.orientPoint, Cell.add, Cell.sub] <;>
        ring
  rw [firstOrigin, secondOrigin]
  exact
    ⟨(AxisDirection.firstCarrierPort direction).outsideCarrierBoundaryAt_add_offset
          origin _ point bounded.1,
      (AxisDirection.secondCarrierPort direction).outsideCarrierBoundaryAt_add_offset
          origin _ point bounded.2⟩

/-- Orientation and translation preserve endpoint-only contact at the
first physical lens endpoint. -/
theorem axisEqualityLensDrawing_routeContactsAt_firstEndpoint
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (axisEqualityLensDrawing
      origin direction span).RouteContactsAtEndpoint origin := by
  have placed :=
    ((horizontalEqualityLensDrawing_routeContactsAt_firstEndpoint
      span).mapPoints direction.orientPoint
        direction.orientPoint_injective).translate origin
  cases direction <;>
    simpa [axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient,
      AxisDirection.orientPoint, Cell.add] using placed

/-- The first physical endpoint-contact certificate can be expressed in
the corresponding macrocell-origin gauge. -/
theorem axisEqualityLensDrawing_routeContactsAt_firstCarrierPort
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (axisEqualityLensDrawing
      origin direction span).RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.firstCarrierMacroOrigin origin direction)
          (AxisDirection.firstCarrierPort direction).position) := by
  simpa [AxisDirection.add_firstCarrierMacroOrigin_portPosition] using
    axisEqualityLensDrawing_routeContactsAt_firstEndpoint
      origin direction span

/-- Orientation and translation preserve endpoint-only contact at the
second physical lens endpoint. -/
theorem axisEqualityLensDrawing_routeContactsAt_secondEndpoint
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (axisEqualityLensDrawing
      origin direction span).RouteContactsAtEndpoint
        (direction.placePoint origin (span, 0)) := by
  exact
    ((horizontalEqualityLensDrawing_routeContactsAt_secondEndpoint
      span).mapPoints direction.orientPoint
        direction.orientPoint_injective).translate origin

/-- The second physical endpoint-contact certificate can be expressed in
the corresponding macrocell-origin gauge. -/
theorem axisEqualityLensDrawing_routeContactsAt_secondCarrierPort
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (axisEqualityLensDrawing
      origin direction span).RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)
          (AxisDirection.secondCarrierPort direction).position) := by
  simpa [AxisDirection.add_secondCarrierMacroOrigin_portPosition] using
    axisEqualityLensDrawing_routeContactsAt_secondEndpoint
      origin direction span

/-- Logical endpoint renaming preserves the two absolute external
carrier-boundary bounds. -/
theorem placedEqualityLensDrawing_routePoints_outsideCarrierBoundaries
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (placedEqualityLensDrawing
      first second origin direction span).RoutePointsSatisfy
      fun point =>
        (AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
            (AxisDirection.firstCarrierMacroOrigin
              origin direction) point ∧
          (AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
            (AxisDirection.secondCarrierMacroOrigin
              origin direction span) point := by
  unfold placedEqualityLensDrawing
  exact
    (axisEqualityLensDrawing_routePoints_outsideCarrierBoundaries
      origin direction span spanLarge).rename _ _

/-- Every route point of a placed lens lies outside the first endpoint
macrocell. -/
theorem placedEqualityLensDrawing_routePoints_outsideFirstCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (placedEqualityLensDrawing
      first second origin direction span).RoutePointsSatisfy
        ((AxisDirection.firstCarrierPort direction).OutsideCarrierBoundaryAt
          (AxisDirection.firstCarrierMacroOrigin origin direction)) := by
  intro incidenceIndex point pointMember
  exact
    (placedEqualityLensDrawing_routePoints_outsideCarrierBoundaries
      first second origin direction span spanLarge
      incidenceIndex point pointMember).1

/-- Every route point of a placed lens lies outside the second endpoint
macrocell. -/
theorem placedEqualityLensDrawing_routePoints_outsideSecondCarrierBoundary
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    (placedEqualityLensDrawing
      first second origin direction span).RoutePointsSatisfy
        ((AxisDirection.secondCarrierPort direction).OutsideCarrierBoundaryAt
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)) := by
  intro incidenceIndex point pointMember
  exact
    (placedEqualityLensDrawing_routePoints_outsideCarrierBoundaries
      first second origin direction span spanLarge
      incidenceIndex point pointMember).2

/-- Logical endpoint renaming preserves endpoint-only contact at the first
physical endpoint. -/
theorem placedEqualityLensDrawing_routeContactsAt_firstEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).RouteContactsAtEndpoint
        origin := by
  unfold placedEqualityLensDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    (axisEqualityLensDrawing_routeContactsAt_firstEndpoint
      origin direction span).rename _ _

/-- The first endpoint-only contact certificate for a renamed lens is
available in its macrocell-origin gauge. -/
theorem placedEqualityLensDrawing_routeContactsAt_firstCarrierPort
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.firstCarrierMacroOrigin origin direction)
          (AxisDirection.firstCarrierPort direction).position) := by
  unfold placedEqualityLensDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    (axisEqualityLensDrawing_routeContactsAt_firstCarrierPort
      origin direction span).rename _ _

/-- Logical endpoint renaming preserves endpoint-only contact at the second
physical endpoint. -/
theorem placedEqualityLensDrawing_routeContactsAt_secondEndpoint
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).RouteContactsAtEndpoint
        (direction.placePoint origin (span, 0)) := by
  unfold placedEqualityLensDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    (axisEqualityLensDrawing_routeContactsAt_secondEndpoint
      origin direction span).rename _ _

/-- The second endpoint-only contact certificate for a renamed lens is
available in its macrocell-origin gauge. -/
theorem placedEqualityLensDrawing_routeContactsAt_secondCarrierPort
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection) (span : Int) :
    (placedEqualityLensDrawing
      first second origin direction span).RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)
          (AxisDirection.secondCarrierPort direction).position) := by
  unfold placedEqualityLensDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    (axisEqualityLensDrawing_routeContactsAt_secondCarrierPort
      origin direction span).rename _ _

/-- Every selected route of a placed lens avoids every selected route of a
drawing certified on the internal side of its first carrier port. -/
theorem placedEqualityLensDrawing_firstCarrier_routesAvoidInsideDrawing
    {Variable InsideVariable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span)
    {insideDrawing :
      EmbeddedCNFIncidenceDrawing InsideVariable}
    (insideBounded :
      insideDrawing.RoutePointsSatisfy
        ((AxisDirection.firstCarrierPort direction).InsideCarrierBoundaryAt
          (AxisDirection.firstCarrierMacroOrigin origin direction)))
    (insideContacts :
      insideDrawing.RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.firstCarrierMacroOrigin origin direction)
          (AxisDirection.firstCarrierPort direction).position))
    (outsideIndex :
      Fin (placedEqualityLensDrawing
        first second origin direction span).incidences.length)
    (insideIndex : Fin insideDrawing.incidences.length) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((placedEqualityLensDrawing
        first second origin direction span).routeAt
          ((placedEqualityLensDrawing
            first second origin direction span).incidenceAt outsideIndex))
      (insideDrawing.routeAt
        (insideDrawing.incidenceAt insideIndex)) := by
  exact
    drawingRoutesAvoidEachOther_of_outside_insideCarrierBoundaryAt
      (AxisDirection.firstCarrierPort direction)
      (AxisDirection.firstCarrierMacroOrigin origin direction)
      (placedEqualityLensDrawing_routePoints_outsideFirstCarrierBoundary
        first second origin direction span spanLarge)
      insideBounded
      (placedEqualityLensDrawing_routeContactsAt_firstCarrierPort
        first second origin direction span)
      insideContacts
      outsideIndex insideIndex

/-- Every selected route of a placed lens avoids every selected route of a
drawing certified on the internal side of its second carrier port. -/
theorem placedEqualityLensDrawing_secondCarrier_routesAvoidInsideDrawing
    {Variable InsideVariable : Type*} [DecidableEq Variable]
    (first second : Variable)
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span)
    {insideDrawing :
      EmbeddedCNFIncidenceDrawing InsideVariable}
    (insideBounded :
      insideDrawing.RoutePointsSatisfy
        ((AxisDirection.secondCarrierPort direction).InsideCarrierBoundaryAt
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)))
    (insideContacts :
      insideDrawing.RouteContactsAtEndpoint
        (Cell.add
          (AxisDirection.secondCarrierMacroOrigin
            origin direction span)
          (AxisDirection.secondCarrierPort direction).position))
    (outsideIndex :
      Fin (placedEqualityLensDrawing
        first second origin direction span).incidences.length)
    (insideIndex : Fin insideDrawing.incidences.length) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((placedEqualityLensDrawing
        first second origin direction span).routeAt
          ((placedEqualityLensDrawing
            first second origin direction span).incidenceAt outsideIndex))
      (insideDrawing.routeAt
        (insideDrawing.incidenceAt insideIndex)) := by
  exact
    drawingRoutesAvoidEachOther_of_outside_insideCarrierBoundaryAt
      (AxisDirection.secondCarrierPort direction)
      (AxisDirection.secondCarrierMacroOrigin origin direction span)
      (placedEqualityLensDrawing_routePoints_outsideSecondCarrierBoundary
        first second origin direction span spanLarge)
      insideBounded
      (placedEqualityLensDrawing_routeContactsAt_secondCarrierPort
        first second origin direction span)
      insideContacts
      outsideIndex insideIndex

end PlanarThreeSAT
end LeanTrominoes
