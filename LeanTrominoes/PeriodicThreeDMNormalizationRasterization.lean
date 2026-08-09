import LeanTrominoes.PeriodicThreeDMVertexNormalizationColors

/-!
# Rasterizing normalized 3DM routes

The three-round normalized geometry consists of unit-step colored routes and
degree-three vertex centers.  This module compiles that finite periodic data
to `PeriodicOrthogonalDrawing`: route interiors become wire/bend cells,
centers become the appropriate vertex cells, and every unused torus position
is blank.

Geometric routes use positive `y` for north, whereas the drawing-cell API uses
row coordinates (north decreases `y`).  `rasterLocation` performs this one
reflection while reducing coordinates modulo the final positive period.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Natural-number form of the per-round magnification. -/
def vertexNormalizationScaleNat : Nat := 12

/-- Period after all three normalization rounds. -/
def PlanarPresentation.finalNormalizationPeriod
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) : Nat :=
  vertexNormalizationScaleNat ^ 3 *
    presentation.contractedDrawing.gridSize

theorem PlanarPresentation.finalNormalizationPeriod_pos
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    0 < presentation.finalNormalizationPeriod := by
  simp [PlanarPresentation.finalNormalizationPeriod,
    vertexNormalizationScaleNat, PeriodicGridDrawing.gridSize]

/-- Reflect north/south and choose the stored representative of a physical
point in the final square torus. -/
def rasterLocation (period : Nat) (point : Cell) : Cell :=
  (point.1 % period, (-point.2) % period)

/-- Convert a geometric direction to the correspondingly named drawing-cell
side after `rasterLocation` has reflected the vertical coordinate. -/
def Side.ofAxisDirection : AxisDirection → Side
  | .east => .east
  | .north => .north
  | .west => .west
  | .south => .south
  | .invalid => .west

/-- Routing cell with ports on the named unordered pair of sides.  Invalid
or immediately reversing local data falls back to blank. -/
def routingCellType (first second : Side)
    (color : WireColor) : OrthogonalCellType :=
  match first, second with
  | .west, .east | .east, .west => .wire .horizontal color
  | .north, .south | .south, .north => .wire .vertical color
  | .north, .east | .east, .north => .bend .northeast color
  | .north, .west | .west, .north => .bend .northwest color
  | .south, .east | .east, .south => .bend .southeast color
  | .south, .west | .west, .south => .bend .southwest color
  | _, _ => .blank

/-- Classify one internal route point from its predecessor and successor. -/
def routingCellTypeAt (before current after : Cell)
    (color : WireColor) : OrthogonalCellType :=
  routingCellType
    (Side.ofAxisDirection (AxisDirection.between current before))
    (Side.ofAxisDirection (AxisDirection.between current after))
    color

/-- One finite-torus assignment before resolving locations to a full cell
array. -/
abbrev NormalizedCellAssignment := Cell × OrthogonalCellType

/-- Assign routing cells to every internal point of a route, excluding its
two vertex endpoints. -/
def routeInteriorAssignments (period : Nat) (color : WireColor) :
    List Cell → List NormalizedCellAssignment
  | before :: current :: after :: rest =>
      (rasterLocation period current,
        routingCellTypeAt before current after color) ::
      routeInteriorAssignments period color (current :: after :: rest)
  | _ => []
termination_by points => points.length

/-- Final vertex assignments, retained ahead of route assignments so the
total lookup has an explicit deterministic priority on malformed inputs. -/
def PlanarPresentation.finalVertexAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  problem.contractedGraph.vertices.map fun vertex =>
    (rasterLocation presentation.finalNormalizationPeriod
      (presentation.finalNormalizationPosition vertex),
      presentation.finalVertexCellType vertex)

/-- Final routing assignments in contracted-edge order. -/
def PlanarPresentation.finalRouteAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  problem.contractedEdges.flatMap fun edge =>
    routeInteriorAssignments presentation.finalNormalizationPeriod
      edge.color (presentation.finalNormalizationRoute edge)

/-- All nonblank assignments used to construct the finite torus array. -/
def PlanarPresentation.finalCellAssignments
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List NormalizedCellAssignment :=
  presentation.finalVertexAssignments ++
    presentation.finalRouteAssignments

/-- Total cell lookup, with blank as the fallback outside the normalized
embedded graph or on malformed intermediate data. -/
def PlanarPresentation.finalCellTypeAt
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (location : Cell) : OrthogonalCellType :=
  (presentation.finalCellAssignments.lookup location).getD .blank

/-- Row-major full torus array consumed by `PeriodicOrthogonalDrawing`. -/
def PlanarPresentation.finalCellTypes
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    List OrthogonalCellType :=
  (List.range presentation.finalNormalizationPeriod).flatMap fun vertical =>
    (List.range presentation.finalNormalizationPeriod).map fun horizontal =>
      presentation.finalCellTypeAt (horizontal, vertical)

/-- Executable normalized drawing compiled from a contracted planar 3DM
presentation. -/
def PlanarPresentation.normalizedOrthogonalDrawing
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    PeriodicOrthogonalDrawing where
  horizontalPeriodPred := presentation.finalNormalizationPeriod - 1
  verticalPeriodPred := presentation.finalNormalizationPeriod - 1
  cellTypes := presentation.finalCellTypes

/-- Both actual periods of the compiled drawing are the advertised final
normalization period. -/
theorem PlanarPresentation.normalizedOrthogonalDrawing_periods
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.normalizedOrthogonalDrawing.horizontalPeriodPred + 1 =
        presentation.finalNormalizationPeriod ∧
      presentation.normalizedOrthogonalDrawing.verticalPeriodPred + 1 =
        presentation.finalNormalizationPeriod := by
  have positive := presentation.finalNormalizationPeriod_pos
  simp [PlanarPresentation.normalizedOrthogonalDrawing,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt positive))]

/-- The row-major compiler emits exactly one entry per torus position. -/
theorem PlanarPresentation.finalCellTypes_length
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalCellTypes.length =
      presentation.finalNormalizationPeriod ^ 2 := by
  unfold PlanarPresentation.finalCellTypes
  rw [List.length_flatMap]
  simp [pow_two]

end PeriodicThreeDM
end LeanTrominoes
