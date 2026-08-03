import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.PlanarOneInThreeNoUnitsFigureNineSelector
import LeanTrominoes.PositionedPeriodicCNFClauseDirectionOrdering

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

end ComposedClauseExitFanData
end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
