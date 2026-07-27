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

end PlanarThreeSAT
end LeanTrominoes
