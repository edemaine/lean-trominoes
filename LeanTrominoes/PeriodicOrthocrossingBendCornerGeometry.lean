import LeanTrominoes.PlanarThreeSATCornerEquality
import LeanTrominoes.PeriodicOrthocrossingPlanarBends
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-!
# Route-bend corner equality geometry

The fixed corner-equality drawing is indexed by two compass ports.  This
file translates a route bend's incoming and outgoing segment directions
into those ports and packages the three geometric facts needed by the local
drawing: both segments are genuine orthogonal segments, and the route does
not reverse immediately at their common endpoint.

Under that interface, the placed drawing is proved to contain the bend's
exact positioned equality formula, to realize both carrier-node positions,
and to retain the complete local validity certificate.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Convert a genuine directed axis to its matching macrocell compass port.
The invalid case is an irrelevant total fallback. -/
def CornerPort.ofDirection : AxisDirection → CornerPort
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .invalid => .west

/-- Compass-port conversion is injective on genuine directed axes. -/
theorem CornerPort.ofDirection_injective_of_genuine
    {first second : AxisDirection}
    (firstGenuine : first.IsGenuine)
    (secondGenuine : second.IsGenuine)
    (equal : ofDirection first = ofDirection second) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [AxisDirection.IsGenuine, ofDirection]

/-- A segment's start terminal uses the compass port in its direction of
travel. -/
theorem segmentTerminalLocalPosition_start_eq_cornerPort
    (segment : GridSegment) (aligned : segment.IsAxisAligned) :
    segmentTerminalLocalPosition segment .start =
      (CornerPort.ofDirection
        (AxisDirection.between segment.start segment.finish)).position := by
  rcases segment with ⟨⟨firstX, firstY⟩, ⟨secondX, secondY⟩⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  simp [segmentTerminalLocalPosition, AxisDirection.between,
    CornerPort.ofDirection, CornerPort.position]
  split_ifs <;> simp_all <;> omega

/-- A segment's finish terminal uses the compass port opposite its direction
of travel. -/
theorem segmentTerminalLocalPosition_finish_eq_cornerPort
    (segment : GridSegment) (aligned : segment.IsAxisAligned) :
    segmentTerminalLocalPosition segment .finish =
      (CornerPort.ofDirection
        (AxisDirection.between
          segment.start segment.finish).opposite).position := by
  rcases segment with ⟨⟨firstX, firstY⟩, ⟨secondX, secondY⟩⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  simp [segmentTerminalLocalPosition, AxisDirection.between,
    AxisDirection.opposite, CornerPort.ofDirection,
    CornerPort.position]
  split_ifs <;> simp_all <;> omega

/-- Compass port occupied by the incoming segment's finish terminal. -/
def RouteBend.incomingPort (routeBend : RouteBend) : CornerPort :=
  CornerPort.ofDirection
    (AxisDirection.between
      routeBend.incomingStart routeBend.bend).opposite

/-- Compass port occupied by the outgoing segment's start terminal. -/
def RouteBend.outgoingPort (routeBend : RouteBend) : CornerPort :=
  CornerPort.ofDirection
    (AxisDirection.between
      routeBend.bend routeBend.outgoingFinish)

/-- The local route facts needed to instantiate a bend's corner equality
drawing. -/
structure RouteBend.CornerGeometry (routeBend : RouteBend) : Prop where
  incomingAligned :
    (GridSegment.mk
      routeBend.incomingStart routeBend.bend).IsAxisAligned
  outgoingAligned :
    (GridSegment.mk
      routeBend.bend routeBend.outgoingFinish).IsAxisAligned
  noReversal :
    AxisDirection.between
        routeBend.bend routeBend.outgoingFinish ≠
      (AxisDirection.between
        routeBend.incomingStart routeBend.bend).opposite

/-- A genuine nonreversing route bend occupies two distinct compass ports. -/
theorem RouteBend.CornerGeometry.portsDifferent
    {routeBend : RouteBend}
    (geometry : routeBend.CornerGeometry) :
    routeBend.incomingPort ≠ routeBend.outgoingPort := by
  intro equal
  apply geometry.noReversal.symm
  apply CornerPort.ofDirection_injective_of_genuine
  · exact AxisDirection.opposite_isGenuine
      (AxisDirection.between_isGenuine_of_axisAligned
        geometry.incomingAligned)
  · exact AxisDirection.between_isGenuine_of_axisAligned
      geometry.outgoingAligned
  · exact equal

/-- The two logical carrier nodes of a bend link are distinct because they
name different segment-end constructors. -/
theorem RouteBend.nodesDifferent
    (routeBend : RouteBend) :
    CarrierNode.terminal routeBend.incomingTerminal ≠
      CarrierNode.terminal routeBend.outgoingTerminal := by
  intro equal
  have terminalEqual :
      routeBend.incomingTerminal =
        routeBend.outgoingTerminal := by
    exact CarrierNode.terminal.inj equal
  have endpointEqual :=
    congrArg SegmentTerminal.endpoint terminalEqual
  simp [RouteBend.incomingTerminal,
    RouteBend.outgoingTerminal] at endpointEqual

/-- Place the fixed corner equality drawing in the macrocell surrounding one
route bend. -/
def RouteBend.cornerDrawing
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    EmbeddedCNFIncidenceDrawing CarrierNode :=
  placedCornerEqualityDrawing
    (.terminal routeBend.incomingTerminal)
    (.terminal routeBend.outgoingTerminal)
    (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
    routeBend.incomingPort routeBend.outgoingPort

/-- The placed corner contains exactly the bend's positioned equality
formula. -/
theorem RouteBend.cornerDrawing_formula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend) :
    (routeBend.cornerDrawing graph).formula =
      equalityInstance
        (routeBend.equalityLink graph).first
        (routeBend.equalityLink graph).second
        (routeBend.equalityLink graph).positions := by
  simpa [RouteBend.cornerDrawing,
    RouteBend.equalityLink, routeBendEqualityPositions] using
    placedCornerEqualityDrawing_formula
      (CarrierNode.terminal routeBend.incomingTerminal)
      (CarrierNode.terminal routeBend.outgoingTerminal)
      (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
      routeBend.incomingPort routeBend.outgoingPort

/-- The first corner endpoint realizes the incoming terminal's carrier
position. -/
theorem RouteBend.cornerDrawing_firstPosition
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry) :
    (routeBend.cornerDrawing graph).variablePosition
        (routeBend.equalityLink graph).first =
      CarrierNode.position graph
        (routeBend.equalityLink graph).first := by
  rw [show
      (routeBend.equalityLink graph).first =
        CarrierNode.terminal routeBend.incomingTerminal by rfl]
  rw [RouteBend.cornerDrawing,
    placedCornerEqualityDrawing_firstPosition
    routeBend.nodesDifferent]
  change
    Cell.add
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        routeBend.incomingPort.position =
      SegmentTerminal.position graph routeBend.incomingTerminal
  rw [show routeBend.incomingPort.position =
      segmentTerminalLocalPosition
        (GridSegment.mk routeBend.incomingStart routeBend.bend)
        .finish by
    symm
    exact segmentTerminalLocalPosition_finish_eq_cornerPort
      (GridSegment.mk routeBend.incomingStart routeBend.bend)
      geometry.incomingAligned]
  rfl

/-- The second corner endpoint realizes the outgoing terminal's carrier
position. -/
theorem RouteBend.cornerDrawing_secondPosition
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry) :
    (routeBend.cornerDrawing graph).variablePosition
        (routeBend.equalityLink graph).second =
      CarrierNode.position graph
        (routeBend.equalityLink graph).second := by
  rw [show
      (routeBend.equalityLink graph).second =
        CarrierNode.terminal routeBend.outgoingTerminal by rfl]
  rw [RouteBend.cornerDrawing,
    placedCornerEqualityDrawing_secondPosition
    routeBend.nodesDifferent]
  change
    Cell.add
        (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
        routeBend.outgoingPort.position =
      SegmentTerminal.position graph routeBend.outgoingTerminal
  rw [show routeBend.outgoingPort.position =
      segmentTerminalLocalPosition
        (GridSegment.mk routeBend.bend routeBend.outgoingFinish)
        .start by
    symm
    exact segmentTerminalLocalPosition_start_eq_cornerPort
      (GridSegment.mk routeBend.bend routeBend.outgoingFinish)
      geometry.outgoingAligned]
  rfl

/-- The three local route facts produce the complete endpoint,
orthogonality, and continuous-planarity certificate for a bend. -/
theorem RouteBend.cornerDrawing_isValid
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (routeBend : RouteBend)
    (geometry : routeBend.CornerGeometry) :
    (routeBend.cornerDrawing graph).IsValid := by
  exact placedCornerEqualityDrawing_isValid
    routeBend.nodesDifferent
    (Cell.scale planarMacroScale (routeBend.drawingPoint graph))
    geometry.portsDifferent

end PeriodicOrthocrossing
end LeanTrominoes
