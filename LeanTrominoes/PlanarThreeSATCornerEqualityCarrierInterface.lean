import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.PlanarThreeSATCornerEquality

/-!
# Carrier-facing boundaries of corner equality drawings

Each compass port splits its macrocell boundary into an external side used
by a straight carrier lens and an internal side used by a corner drawing.
The two closed regions meet only at the port itself.  This file packages
that geometry and proves a generic route-separation theorem across the
interface.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

/-- The closed macrocell side reserved for a local drawing at one compass
port. -/
def CornerPort.InsideCarrierBoundary :
    CornerPort → Cell → Prop
  | .west, point =>
      1 ≤ point.1 ∧ (point.1 = 1 → 6 ≤ point.2)
  | .east, point =>
      point.1 ≤ 11 ∧ (point.1 = 11 → point.2 ≤ 6)
  | .south, point =>
      1 ≤ point.2 ∧ (point.2 = 1 → point.1 ≤ 6)
  | .north, point =>
      point.2 ≤ 11 ∧ (point.2 = 11 → 6 ≤ point.1)

instance (port : CornerPort) (point : Cell) :
    Decidable (port.InsideCarrierBoundary point) := by
  cases port <;>
    unfold CornerPort.InsideCarrierBoundary <;>
    infer_instance

/-- The closed external side occupied by a straight carrier ending at one
compass port. -/
def CornerPort.OutsideCarrierBoundary :
    CornerPort → Cell → Prop
  | .west, point =>
      point.1 ≤ 1 ∧ (point.1 = 1 → point.2 ≤ 6)
  | .east, point =>
      11 ≤ point.1 ∧ (point.1 = 11 → 6 ≤ point.2)
  | .south, point =>
      point.2 ≤ 1 ∧ (point.2 = 1 → 6 ≤ point.1)
  | .north, point =>
      11 ≤ point.2 ∧ (point.2 = 11 → point.1 ≤ 6)

instance (port : CornerPort) (point : Cell) :
    Decidable (port.OutsideCarrierBoundary point) := by
  cases port <;>
    unfold CornerPort.OutsideCarrierBoundary <;>
    infer_instance

/-- Absolute form of the internal port region for a macrocell with the
given origin. -/
def CornerPort.InsideCarrierBoundaryAt
    (port : CornerPort) (origin point : Cell) : Prop :=
  port.InsideCarrierBoundary (Cell.sub point origin)

instance (port : CornerPort) (origin point : Cell) :
    Decidable (port.InsideCarrierBoundaryAt origin point) := by
  unfold CornerPort.InsideCarrierBoundaryAt
  infer_instance

/-- Absolute form of the external port region for a macrocell with the
given origin. -/
def CornerPort.OutsideCarrierBoundaryAt
    (port : CornerPort) (origin point : Cell) : Prop :=
  port.OutsideCarrierBoundary (Cell.sub point origin)

instance (port : CornerPort) (origin point : Cell) :
    Decidable (port.OutsideCarrierBoundaryAt origin point) := by
  unfold CornerPort.OutsideCarrierBoundaryAt
  infer_instance

/-- Translating an internal local point by the macrocell origin realizes the
absolute internal predicate. -/
theorem CornerPort.insideCarrierBoundaryAt_add
    (port : CornerPort) (origin point : Cell)
    (inside : port.InsideCarrierBoundary point) :
    port.InsideCarrierBoundaryAt origin
      (Cell.add origin point) := by
  simpa [CornerPort.InsideCarrierBoundaryAt,
    Cell.sub, Cell.add] using inside

/-- Translating an external local point by the macrocell origin realizes the
absolute external predicate. -/
theorem CornerPort.outsideCarrierBoundaryAt_add
    (port : CornerPort) (origin point : Cell)
    (outside : port.OutsideCarrierBoundary point) :
    port.OutsideCarrierBoundaryAt origin
      (Cell.add origin point) := by
  simpa [CornerPort.OutsideCarrierBoundaryAt,
    Cell.sub, Cell.add] using outside

/-- Translating both an absolute external region and its point by the same
offset preserves external containment. -/
theorem CornerPort.outsideCarrierBoundaryAt_add_offset
    (port : CornerPort) (offset origin point : Cell)
    (outside : port.OutsideCarrierBoundaryAt origin point) :
    port.OutsideCarrierBoundaryAt
      (Cell.add offset origin) (Cell.add offset point) := by
  simpa [CornerPort.OutsideCarrierBoundaryAt,
    Cell.sub, Cell.add] using outside

/-- The internal and external port regions have exactly one common lattice
point. -/
theorem CornerPort.eq_position_of_inside_of_outside
    (port : CornerPort) {point : Cell}
    (inside : port.InsideCarrierBoundary point)
    (outside : port.OutsideCarrierBoundary point) :
    point = port.position := by
  rcases point with ⟨x, y⟩
  cases port <;>
    simp [CornerPort.InsideCarrierBoundary,
      CornerPort.OutsideCarrierBoundary,
      CornerPort.position] at inside outside ⊢ <;>
    omega

/-- Segment interiors cannot meet across one carrier-facing port boundary
when both endpoints remain on their advertised sides. -/
theorem CornerPort.not_interiorsMeet_of_outside_inside
    (port : CornerPort)
    {outside inside : GridSegment}
    (outsideStart :
      port.OutsideCarrierBoundary outside.start)
    (outsideFinish :
      port.OutsideCarrierBoundary outside.finish)
    (insideStart :
      port.InsideCarrierBoundary inside.start)
    (insideFinish :
      port.InsideCarrierBoundary inside.finish) :
    ¬GridSegment.InteriorsMeet outside inside := by
  rcases outside with
    ⟨⟨outsideStartX, outsideStartY⟩,
      ⟨outsideFinishX, outsideFinishY⟩⟩
  rcases inside with
    ⟨⟨insideStartX, insideStartY⟩,
      ⟨insideFinishX, insideFinishY⟩⟩
  cases port <;>
    simp only [CornerPort.InsideCarrierBoundary,
      CornerPort.OutsideCarrierBoundary]
      at outsideStart outsideFinish insideStart insideFinish <;>
    simp only [GridSegment.InteriorsMeet,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween] <;>
    simp_all [min_def, max_def] <;>
    omega

/-- An external point cannot lie in the relative interior of an internal
axis-aligned segment at the same port boundary. -/
theorem CornerPort.not_interiorContains_inside_of_outside
    (port : CornerPort)
    {point : Cell} {inside : GridSegment}
    (pointOutside :
      port.OutsideCarrierBoundary point)
    (insideStart :
      port.InsideCarrierBoundary inside.start)
    (insideFinish :
      port.InsideCarrierBoundary inside.finish) :
    ¬inside.InteriorContains point := by
  rcases point with ⟨pointX, pointY⟩
  rcases inside with
    ⟨⟨insideStartX, insideStartY⟩,
      ⟨insideFinishX, insideFinishY⟩⟩
  cases port <;>
    simp only [CornerPort.InsideCarrierBoundary,
      CornerPort.OutsideCarrierBoundary]
      at pointOutside insideStart insideFinish <;>
    simp only [GridSegment.InteriorContains,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.StrictlyBetween] <;>
    omega

/-- An internal point cannot lie in the relative interior of an external
axis-aligned segment at the same port boundary. -/
theorem CornerPort.not_interiorContains_outside_of_inside
    (port : CornerPort)
    {point : Cell} {outside : GridSegment}
    (pointInside :
      port.InsideCarrierBoundary point)
    (outsideStart :
      port.OutsideCarrierBoundary outside.start)
    (outsideFinish :
      port.OutsideCarrierBoundary outside.finish) :
    ¬outside.InteriorContains point := by
  rcases point with ⟨pointX, pointY⟩
  rcases outside with
    ⟨⟨outsideStartX, outsideStartY⟩,
      ⟨outsideFinishX, outsideFinishY⟩⟩
  cases port <;>
    simp only [CornerPort.InsideCarrierBoundary,
      CornerPort.OutsideCarrierBoundary]
      at pointInside outsideStart outsideFinish <;>
    simp only [GridSegment.InteriorContains,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.StrictlyBetween] <;>
    omega

/-- Pointwise containment on opposite sides of one port boundary gives
complete route separation, provided any occurrence of the common port is
an advertised endpoint of each route. -/
theorem routesAvoidEachOther_of_outside_insideCarrierBoundary
    (port : CornerPort)
    {outside inside : List Cell}
    (outsideBounded :
      ∀ point ∈ outside,
        port.OutsideCarrierBoundary point)
    (insideBounded :
      ∀ point ∈ inside,
        port.InsideCarrierBoundary point)
    (outsidePortEndpoint :
      ∀ point ∈ outside,
        point = port.position →
          EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            outside point)
    (insidePortEndpoint :
      ∀ point ∈ inside,
        point = port.position →
          EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint
            inside point) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      outside inside := by
  unfold EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro outsideIndex insideIndex
    have outsideEndpoints :=
      gridPolylineSegments_endpoints_mem
        (List.get_mem
          (gridPolylineSegments outside) outsideIndex)
    have insideEndpoints :=
      gridPolylineSegments_endpoints_mem
        (List.get_mem
          (gridPolylineSegments inside) insideIndex)
    exact
      port.not_interiorsMeet_of_outside_inside
        (outsideBounded _ outsideEndpoints.1)
        (outsideBounded _ outsideEndpoints.2)
        (insideBounded _ insideEndpoints.1)
        (insideBounded _ insideEndpoints.2)
  · intro outsidePointIndex insideSegmentIndex
    have insideEndpoints :=
      gridPolylineSegments_endpoints_mem
        (List.get_mem
          (gridPolylineSegments inside) insideSegmentIndex)
    exact
      port.not_interiorContains_inside_of_outside
        (outsideBounded _
          (List.get_mem outside outsidePointIndex))
        (insideBounded _ insideEndpoints.1)
        (insideBounded _ insideEndpoints.2)
  · intro insidePointIndex outsideSegmentIndex
    have outsideEndpoints :=
      gridPolylineSegments_endpoints_mem
        (List.get_mem
          (gridPolylineSegments outside) outsideSegmentIndex)
    exact
      port.not_interiorContains_outside_of_inside
        (insideBounded _
          (List.get_mem inside insidePointIndex))
        (outsideBounded _ outsideEndpoints.1)
        (outsideBounded _ outsideEndpoints.2)
  · intro outsidePointIndex insidePointIndex pointsEqual
    have outsideMember :=
      List.get_mem outside outsidePointIndex
    have insideMember :=
      List.get_mem inside insidePointIndex
    have portEqual :
        outside.get outsidePointIndex = port.position :=
      port.eq_position_of_inside_of_outside
        (by
          rw [pointsEqual]
          exact insideBounded _ insideMember)
        (outsideBounded _ outsideMember)
    exact
      ⟨outsidePortEndpoint _ outsideMember portEqual,
        insidePortEndpoint _ insideMember
          (pointsEqual.symm.trans portEqual)⟩

/-- Every route point in a fixed corner drawing remains on the macrocell
side of both occupied compass-port boundaries. -/
theorem cornerEqualityDrawing_routePoints_insideCarrierBoundaries
    (first second : CornerPort) :
    (cornerEqualityDrawing first second).RoutePointsSatisfy
      fun point =>
        first.InsideCarrierBoundary point ∧
          second.InsideCarrierBoundary point := by
  cases first <;> cases second <;> native_decide

/-- Translating a corner drawing to its macrocell origin preserves both
port-side route bounds. -/
theorem translatedCornerEqualityDrawing_routePoints_insideCarrierBoundaries
    (first second : CornerPort) (origin : Cell) :
    ((cornerEqualityDrawing first second).translate origin).RoutePointsSatisfy
      fun point =>
        first.InsideCarrierBoundaryAt origin point ∧
          second.InsideCarrierBoundaryAt origin point := by
  exact
    (cornerEqualityDrawing_routePoints_insideCarrierBoundaries
      first second).translate origin
      (fun point bounded =>
        ⟨first.insideCarrierBoundaryAt_add origin point bounded.1,
          second.insideCarrierBoundaryAt_add origin point bounded.2⟩)

/-- Logical endpoint renaming does not change the absolute port-side bounds
of a translated corner drawing. -/
theorem placedCornerEqualityDrawing_routePoints_insideCarrierBoundaries
    {Variable : Type*} [DecidableEq Variable]
    (first second : Variable) (origin : Cell)
    (firstPort secondPort : CornerPort) :
    (placedCornerEqualityDrawing
      first second origin firstPort secondPort).RoutePointsSatisfy
        fun point =>
          firstPort.InsideCarrierBoundaryAt origin point ∧
            secondPort.InsideCarrierBoundaryAt origin point := by
  unfold placedCornerEqualityDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    (translatedCornerEqualityDrawing_routePoints_insideCarrierBoundaries
      firstPort secondPort origin).rename _ _

end PlanarThreeSAT
end LeanTrominoes
