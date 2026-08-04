import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineSelector
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# Noncrossing fans from composed Figure 9 ports to source exits

The composed Figure 9-plus-unit-elimination neighborhood has three fixed
source ports.  After the original source route is scaled by the combined
factor `72`, its first exit is one of the four radius-`72` cardinal points.
This file gives a finite outer-frame routing family between those endpoints.

The family is indexed by at most three genuine directions in strictly
increasing clockwise rank.  These are precisely the fourteen direction
subsets produced by clause-direction ordering: four unary, six binary, and
four ternary configurations.  All endpoint, orthogonality, frame, and
pairwise continuous-separation claims are checked directly by Lean.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

/-- A finite family of one, two, or three source exits. -/
structure ComposedClauseExitFanData where
  countPred : Fin 3
  direction : Fin 3 → AxisDirection
  deriving DecidableEq, Fintype

namespace ComposedClauseExitFanData

/-- Number of active source occurrences. -/
def count (data : ComposedClauseExitFanData) : Nat :=
  data.countPred + 1

/-- Whether one of the three source-port slots is active. -/
def SlotActive
    (data : ComposedClauseExitFanData) (slot : Fin 3) : Prop :=
  slot.val < data.count

instance (data : ComposedClauseExitFanData) (slot : Fin 3) :
    Decidable (data.SlotActive slot) := by
  unfold SlotActive
  infer_instance

/-- Genuine directions in strictly increasing clockwise rank. -/
def IsValid (data : ComposedClauseExitFanData) : Prop :=
  (∀ slot, data.SlotActive slot → (data.direction slot).IsGenuine) ∧
    ∀ first second,
      data.SlotActive first → data.SlotActive second →
      first.val < second.val →
      (data.direction first).clockwiseRank <
        (data.direction second).clockwiseRank

instance (data : ComposedClauseExitFanData) :
    Decidable data.IsValid := by
  unfold IsValid
  infer_instance

/-- Radius-`72` first exit selected by one cardinal direction. -/
def sourceExit (direction : AxisDirection) : Cell :=
  Cell.scale composedGadgetScale direction.step

/-- The safe frame outside the open composed-gadget rectangle. -/
def InOuterFrame (point : Cell) : Prop :=
  point.2 ≤ 0 ∨ point.1 ≤ 0 ∨ point.1 ≥ composedGadgetScale

instance (point : Cell) : Decidable (InOuterFrame point) := by
  unfold InOuterFrame
  infer_instance

/-- One selected port-to-exit route.  The cases not admitted by `IsValid`
are harmless total fallbacks; the verified cases are the fourteen genuine
strictly ordered fans. -/
def route
    (data : ComposedClauseExitFanData) (slot : Fin 3) : List Cell :=
  match slot.val, data.direction slot with
  | 0, .east => [(36, 0), (72, 0)]
  | 0, .south => [(36, 0), (36, -73), (0, -73), (0, -72)]
  | 0, .west =>
      [(36, 0), (36, -73), (-73, -73), (-73, 0), (-72, 0)]
  | 0, .north =>
      [(36, 0), (73, 0), (73, 73), (0, 73), (0, 72)]
  | 1, .south => [(0, 30), (0, -72)]
  | 1, .west => [(0, 30), (-73, 30), (-73, 0), (-72, 0)]
  | 1, .north => [(0, 30), (0, 72)]
  | 2, .west =>
      [(72, 30), (73, 30), (73, 73), (-73, 73),
        (-73, 0), (-72, 0)]
  | 2, .north =>
      [(72, 30), (73, 30), (73, 73), (0, 73), (0, 72)]
  | _, _ => []

/-- Every active route begins at its index-selected composed source port. -/
@[simp]
theorem route_head? :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        (data.route slot).head? =
          some (sourceLocalPosition slot.val) := by
  native_decide

/-- Every active route ends at its direction-selected scaled source exit. -/
@[simp]
theorem route_getLast? :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        (data.route slot).getLast? =
          some (sourceExit (data.direction slot)) := by
  native_decide

/-- Every active connector is rectilinear. -/
theorem route_orthogonal :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        OrthogonalPolyline (data.route slot) := by
  native_decide

/-- Every listed connector point stays outside the open composed-gadget
rectangle. -/
theorem route_points_inOuterFrame :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        ∀ point ∈ data.route slot, InOuterFrame point := by
  native_decide

/-- Every active connector stays in the closed radius-`73` square around
the source-clause origin.  This includes the one-cell outer clearance used
by the west, north, and south detours. -/
theorem route_points_within_sourceNeighborhood :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ slot, data.SlotActive slot →
        ∀ point ∈ data.route slot,
          WithinCoordinateRadius 73 (0, 0) point := by
  native_decide

/-- Distinct active connectors have no continuous or listed-point contact. -/
theorem routes_strictlyAvoidEachOther :
    ∀ (data : ComposedClauseExitFanData),
      data.IsValid →
      ∀ first second,
        data.SlotActive first → data.SlotActive second →
      first ≠ second →
      RoutesStrictlyAvoidEachOther
        (data.route first) (data.route second) := by
  native_decide

/-! ## Isolation from the finite composed local drawings -/

/-- In every ternary-source template, a local route and an active exit-fan
connector are strictly separated unless their variable/source-port
endpoints are the same. -/
theorem fullDrawingFor_routeAt_strictlyAvoids_route :
    ∀ (first second third : Bool)
      (data : ComposedClauseExitFanData)
      (localIndex : Fin
        (fullDrawingFor first second third).incidences.length)
      (slot : Fin 3),
      data.IsValid → data.SlotActive slot →
      ((fullDrawingFor first second third).routeAt
          ((fullDrawingFor first second third).incidenceAt
            localIndex)).getLast? ≠
        (data.route slot).head? →
      RoutesStrictlyAvoidEachOther
        ((fullDrawingFor first second third).routeAt
          ((fullDrawingFor first second third).incidenceAt
            localIndex))
        (data.route slot) := by
  native_decide

/-- Binary-source version of
`fullDrawingFor_routeAt_strictlyAvoids_route`. -/
theorem twoDrawingFor_routeAt_strictlyAvoids_route :
    ∀ (first second : Bool)
      (data : ComposedClauseExitFanData)
      (localIndex : Fin
        (twoDrawingFor first second).incidences.length)
      (slot : Fin 3),
      data.IsValid → data.SlotActive slot →
      ((twoDrawingFor first second).routeAt
          ((twoDrawingFor first second).incidenceAt
            localIndex)).getLast? ≠
        (data.route slot).head? →
      RoutesStrictlyAvoidEachOther
        ((twoDrawingFor first second).routeAt
          ((twoDrawingFor first second).incidenceAt
            localIndex))
        (data.route slot) := by
  native_decide

/-- Unit-source version of
`fullDrawingFor_routeAt_strictlyAvoids_route`. -/
theorem oneDrawingFor_routeAt_strictlyAvoids_route :
    ∀ (first : Bool)
      (data : ComposedClauseExitFanData)
      (localIndex : Fin
        (oneDrawingFor first).incidences.length)
      (slot : Fin 3),
      data.IsValid → data.SlotActive slot →
      ((oneDrawingFor first).routeAt
          ((oneDrawingFor first).incidenceAt
            localIndex)).getLast? ≠
        (data.route slot).head? →
      RoutesStrictlyAvoidEachOther
        ((oneDrawingFor first).routeAt
          ((oneDrawingFor first).incidenceAt
            localIndex))
        (data.route slot) := by
  native_decide

/-- Empty-source version of
`fullDrawingFor_routeAt_strictlyAvoids_route`. -/
theorem zeroDrawing_routeAt_strictlyAvoids_route :
    ∀ (data : ComposedClauseExitFanData)
      (localIndex : Fin zeroDrawing.incidences.length)
      (slot : Fin 3),
      data.IsValid → data.SlotActive slot →
      (zeroDrawing.routeAt
          (zeroDrawing.incidenceAt localIndex)).getLast? ≠
        (data.route slot).head? →
      RoutesStrictlyAvoidEachOther
        (zeroDrawing.routeAt
          (zeroDrawing.incidenceAt localIndex))
        (data.route slot) := by
  native_decide

/-- Uniform selector form of the four finite local-route/exit-connector
checks. -/
theorem templateDrawing_routeAt_strictlyAvoids_route
    {Variable : Type*}
    (source : PositionedPeriodicClause Variable)
    (width : source.literals.length ≤ 3)
    (data : ComposedClauseExitFanData)
    (localIndex : Fin (templateDrawing source).incidences.length)
    (slot : Fin 3)
    (valid : data.IsValid)
    (active : data.SlotActive slot)
    (endpointsDifferent :
      ((templateDrawing source).routeAt
          ((templateDrawing source).incidenceAt localIndex)).getLast? ≠
        (data.route slot).head?) :
    RoutesStrictlyAvoidEachOther
      ((templateDrawing source).routeAt
        ((templateDrawing source).incidenceAt localIndex))
      (data.route slot) := by
  rcases source with ⟨sourcePosition, literals⟩
  rcases literals with _ | ⟨first, tail⟩
  · exact zeroDrawing_routeAt_strictlyAvoids_route
      data localIndex slot valid active endpointsDifferent
  · rcases tail with _ | ⟨second, tail⟩
    · exact oneDrawingFor_routeAt_strictlyAvoids_route
        first.value data localIndex slot valid active
        endpointsDifferent
    · rcases tail with _ | ⟨third, tail⟩
      · exact twoDrawingFor_routeAt_strictlyAvoids_route
          first.value second.value data localIndex slot
          valid active endpointsDifferent
      · have tailEmpty : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp at width
          omega
        subst tail
        exact fullDrawingFor_routeAt_strictlyAvoids_route
          first.value second.value third.value data localIndex slot
          valid active endpointsDifferent

end ComposedClauseExitFanData
end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
