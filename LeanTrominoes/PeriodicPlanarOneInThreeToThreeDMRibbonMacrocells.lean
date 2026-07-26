import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation
import LeanTrominoes.OrthogonalPolylineUnitSubdivision
import LeanTrominoes.OrthogonalPolylineRibbonTurnGeometry

/-!
# Half-edge ribbon tiles for 3DM corridors

A turn template centered at every source lattice point must not extend all
the way to its neighboring source points: adjacent templates would then
retrace half of each other's route.  We instead use half-edge tiles in the
`128`-fold refinement.  Every tile runs from distance `64` before its center
to distance `64` after it.  Consecutive tiles therefore meet at exactly their
common macrocell boundary.

The three colored lanes use the already selected normal distances
`40`, `44`, and `48`.  All legal straight and quarter-turn cases are finite,
so simplicity, orthogonality, and pairwise continuous separation are checked
exhaustively once at the origin and transported to every source lattice
point by translation.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Half the `128`-cell spacing between neighboring refined source points. -/
def standardRibbonMacrocellHalfSpan : Int := 64

theorem standardRibbonMacrocellHalfSpan_positive :
    0 < standardRibbonMacrocellHalfSpan := by
  decide

theorem standardRibbonMacrocellHalfSpan_twice :
    2 * standardRibbonMacrocellHalfSpan =
      standardThreeStrandLayout.factor := by
  decide

/-- Local point where an incoming lane enters the macrocell centered at the
origin. -/
def standardRibbonMacrocellEntry
    (incoming : AxisDirection) (color : WireColor) : Cell :=
  Cell.add
    (Cell.scale (-standardRibbonMacrocellHalfSpan) incoming.step)
    (incoming.rightNormal (standardRibbonLaneDistance color))

/-- Local point where an outgoing lane exits the macrocell centered at the
origin. -/
def standardRibbonMacrocellExit
    (outgoing : AxisDirection) (color : WireColor) : Cell :=
  Cell.add
    (Cell.scale standardRibbonMacrocellHalfSpan outgoing.step)
    (outgoing.rightNormal (standardRibbonLaneDistance color))

/-- One colored half-edge tile at the origin.  Inside turns are trimmed to
the intersection of their two offset lines; outside turns follow the other
three sides of the normal-offset rectangle. -/
def standardRibbonMacrocellRoute
    (incoming outgoing : AxisDirection)
    (color : WireColor) : List Cell :=
  let distance := standardRibbonLaneDistance color
  let first := standardRibbonMacrocellEntry incoming color
  let incomingAtCenter := incoming.rightNormal distance
  let outgoingAtCenter := outgoing.rightNormal distance
  let middle := Cell.add incomingAtCenter outgoingAtCenter
  let last := standardRibbonMacrocellExit outgoing color
  if incoming = outgoing then
    [first, incomingAtCenter, last]
  else if outgoing = incoming.opposite then
    [first, incomingAtCenter, outgoingAtCenter, last]
  else if incoming.TurnsRight outgoing then
    [first, middle, last]
  else
    [first, incomingAtCenter, middle, outgoingAtCenter, last]

@[simp]
theorem standardRibbonMacrocellRoute_head?
    (incoming outgoing : AxisDirection) (color : WireColor) :
    (standardRibbonMacrocellRoute incoming outgoing color).head? =
      some (standardRibbonMacrocellEntry incoming color) := by
  unfold standardRibbonMacrocellRoute
  split_ifs <;> rfl

@[simp]
theorem standardRibbonMacrocellRoute_getLast?
    (incoming outgoing : AxisDirection) (color : WireColor) :
    (standardRibbonMacrocellRoute incoming outgoing color).getLast? =
      some (standardRibbonMacrocellExit outgoing color) := by
  unfold standardRibbonMacrocellRoute
  split_ifs <;> rfl

/-- Every legal standard macrocell lane is rectilinear. -/
theorem standardRibbonMacrocellRoute_orthogonal
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (color : WireColor) :
    OrthogonalPolyline
      (standardRibbonMacrocellRoute incoming outgoing color) := by
  cases incoming <;> cases outgoing <;> cases color <;>
    simp_all [AxisDirection.IsGenuine,
      AxisDirection.opposite, standardRibbonMacrocellRoute,
      standardRibbonMacrocellEntry,
      standardRibbonMacrocellExit,
      standardRibbonMacrocellHalfSpan,
      standardRibbonLaneDistance,
      AxisDirection.step, AxisDirection.rightNormal,
      AxisDirection.TurnsRight, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, Cell.add, Cell.scale]

/-- Every legal standard macrocell lane is geometrically simple. -/
theorem standardRibbonMacrocellRoute_simple
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (standardRibbonMacrocellRoute incoming outgoing color) := by
  cases incoming <;> cases outgoing <;> cases color <;>
    simp_all [AxisDirection.IsGenuine,
      AxisDirection.opposite] <;>
    native_decide

/-- Distinct colored lanes in one legal standard macrocell are continuously
separated. -/
theorem standardRibbonMacrocellRoutes_avoidEachOther
    {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    {first second : WireColor}
    (different : first ≠ second) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (standardRibbonMacrocellRoute incoming outgoing first)
      (standardRibbonMacrocellRoute incoming outgoing second) := by
  cases incoming <;> cases outgoing <;>
    cases first <;> cases second <;>
    simp_all [AxisDirection.IsGenuine,
      AxisDirection.opposite] <;>
    native_decide

/-- Refined origin of the macrocell centered at a source lattice point. -/
def ribbonMacrocellOrigin (center : Cell) : Cell :=
  Cell.scale standardThreeStrandLayout.factor center

/-- Entry boundary point of a translated colored macrocell tile. -/
def ribbonMacrocellEntry
    (center : Cell) (incoming : AxisDirection)
    (color : WireColor) : Cell :=
  Cell.add (ribbonMacrocellOrigin center)
    (standardRibbonMacrocellEntry incoming color)

/-- Exit boundary point of a translated colored macrocell tile. -/
def ribbonMacrocellExit
    (center : Cell) (outgoing : AxisDirection)
    (color : WireColor) : Cell :=
  Cell.add (ribbonMacrocellOrigin center)
    (standardRibbonMacrocellExit outgoing color)

/-- Translate a standard half-edge tile into the macrocell centered at a
source lattice point. -/
def ribbonMacrocellRoute
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : WireColor) : List Cell :=
  (standardRibbonMacrocellRoute incoming outgoing color).map
    (Cell.add (ribbonMacrocellOrigin center))

@[simp]
theorem ribbonMacrocellRoute_head?
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : WireColor) :
    (ribbonMacrocellRoute center incoming outgoing color).head? =
      some (ribbonMacrocellEntry center incoming color) := by
  simp [ribbonMacrocellRoute, ribbonMacrocellEntry]

@[simp]
theorem ribbonMacrocellRoute_getLast?
    (center : Cell) (incoming outgoing : AxisDirection)
    (color : WireColor) :
    (ribbonMacrocellRoute center incoming outgoing color).getLast? =
      some (ribbonMacrocellExit center outgoing color) := by
  simp [ribbonMacrocellRoute, ribbonMacrocellExit]

/-- Neighboring source macrocells assign exactly the same point to their
shared colored half-edge boundary. -/
theorem ribbonMacrocellExit_eq_entry_next
    (center : Cell) (direction : AxisDirection)
    (color : WireColor) :
    ribbonMacrocellExit center direction color =
      ribbonMacrocellEntry
        (Cell.add center direction.step) direction color := by
  rcases center with ⟨centerX, centerY⟩
  cases direction <;> cases color <;>
    simp [ribbonMacrocellExit, ribbonMacrocellEntry,
      ribbonMacrocellOrigin, standardRibbonMacrocellExit,
      standardRibbonMacrocellEntry,
      standardRibbonMacrocellHalfSpan,
      standardThreeStrandLayout, standardRibbonLaneDistance,
      AxisDirection.step, AxisDirection.rightNormal,
      Cell.add, Cell.scale] <;>
    omega

/-- The two tiles on the ends of a genuine unit source edge assign the same
colored point to their shared boundary. -/
theorem ribbonMacrocellExit_eq_entry_of_unitAxisStep
    {source target : Cell}
    (unit : AxisDirection.IsUnitAxisStep source target)
    (color : WireColor) :
    ribbonMacrocellExit source
        (AxisDirection.between source target) color =
      ribbonMacrocellEntry target
        (AxisDirection.between source target) color := by
  let direction := AxisDirection.between source target
  calc
    ribbonMacrocellExit source direction color =
        ribbonMacrocellEntry
          (Cell.add source direction.step) direction color :=
      ribbonMacrocellExit_eq_entry_next source direction color
    _ = ribbonMacrocellEntry target direction color := by
      rw [← AxisDirection.add_between_step_eq_of_unitAxisStep unit]

/-- Translation preserves rectilinearity of a legal macrocell lane. -/
theorem ribbonMacrocellRoute_orthogonal
    (center : Cell) {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (color : WireColor) :
    OrthogonalPolyline
      (ribbonMacrocellRoute center incoming outgoing color) := by
  unfold ribbonMacrocellRoute OrthogonalPolyline
  apply List.isChain_map_of_isChain
      (Cell.add (ribbonMacrocellOrigin center))
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second)
        (ribbonMacrocellOrigin center)).2 aligned
  · exact standardRibbonMacrocellRoute_orthogonal
      incomingGenuine outgoingGenuine noReverse color

/-- Translation preserves simplicity of a legal macrocell lane. -/
theorem ribbonMacrocellRoute_simple
    (center : Cell) {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (ribbonMacrocellRoute center incoming outgoing color) := by
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      (standardRibbonMacrocellRoute_simple
        incomingGenuine outgoingGenuine noReverse color)
      (ribbonMacrocellOrigin center)

/-- Translation preserves continuous separation between distinct colored
lanes in a legal macrocell. -/
theorem ribbonMacrocellRoutes_avoidEachOther
    (center : Cell) {incoming outgoing : AxisDirection}
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    {first second : WireColor}
    (different : first ≠ second) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (ribbonMacrocellRoute center incoming outgoing first)
      (ribbonMacrocellRoute center incoming outgoing second) := by
  exact
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_translate
      (standardRibbonMacrocellRoutes_avoidEachOther
        incomingGenuine outgoingGenuine noReverse different)
      (ribbonMacrocellOrigin center)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
