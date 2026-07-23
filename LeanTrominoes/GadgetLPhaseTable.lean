import LeanTrominoes.GadgetPortRefinement

/-!
# Verified geometric phase laws for the Figure 11 L gadgets

Boolean port values forget which supported geometric boundary state crosses
an interface.  Exhaustive native certificates in this file establish the
closure properties needed to recover those phases globally: route-end phases
can be recombined, one side of any local state can be spliced independently,
and complementary same-color half-edges always admit matching exact ports.
-/

namespace LeanTrominoes
namespace Gadget

/-- Ordered incident sides of a degree-two routing cell. -/
def OrthogonalCellType.routingSides :
    OrthogonalCellType → Option (Side × Side)
  | .wire .horizontal _ => some (.west, .east)
  | .wire .vertical _ => some (.north, .south)
  | .bend .northeast _ => some (.north, .east)
  | .bend .northwest _ => some (.north, .west)
  | .bend .southeast _ => some (.south, .east)
  | .bend .southwest _ => some (.south, .west)
  | _ => none

/-- A supported entry realizes the requested Boolean values on every colored
side of its cell. -/
def LEntryRealizes
    (entry : OrthogonalCellType × PortConfiguration)
    (inward : Side → Bool) : Prop :=
  ∀ side, (entry.1.portColor side).isSome →
    lConfigurationInward entry.1 entry.2 side = inward side

instance (entry : OrthogonalCellType × PortConfiguration)
    (inward : Side → Bool) : Decidable (LEntryRealizes entry inward) := by
  unfold LEntryRealizes
  infer_instance

abbrev LSupportedEntry :=
  { entry // entry ∈ supportedCellPortTable .L }

structure LRoutingComparison where
  cellType : OrthogonalCellType
  inward : Side → Bool
  first : Side
  second : Side
  left : LSupportedEntry
  right : LSupportedEntry
  deriving Fintype

/-- At a routing cell, phases available on the two incident sides can be
combined independently while preserving the Boolean orientation. -/
def LRoutingPhaseRectangular : Prop :=
  ∀ comparison : LRoutingComparison,
    comparison.cellType.routingSides =
        some (comparison.first, comparison.second) →
      comparison.left.1.1 = comparison.cellType →
      comparison.right.1.1 = comparison.cellType →
      LEntryRealizes comparison.left.1 comparison.inward →
      LEntryRealizes comparison.right.1 comparison.inward →
        ∃ combined : LSupportedEntry,
          combined.1.1 = comparison.cellType ∧
            LEntryRealizes combined.1 comparison.inward ∧
              combined.1.2.get comparison.first =
                  comparison.left.1.2.get comparison.first ∧
                combined.1.2.get comparison.second =
                  comparison.right.1.2.get comparison.second

instance : Decidable LRoutingPhaseRectangular := by
  unfold LRoutingPhaseRectangular
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lRoutingPhaseRectangular : LRoutingPhaseRectangular := by
  native_decide

/-- One port phase can be taken from one realization and spliced into all
the other port phases of another realization of the same local Boolean
orientation. -/
def LCellPhaseSplice : Prop :=
  ∀ comparison : LRoutingComparison,
    comparison.left.1.1 = comparison.cellType →
      comparison.right.1.1 = comparison.cellType →
      LEntryRealizes comparison.left.1 comparison.inward →
      LEntryRealizes comparison.right.1 comparison.inward →
        ∃ combined : LSupportedEntry,
          combined.1.1 = comparison.cellType ∧
            LEntryRealizes combined.1 comparison.inward ∧
              combined.1.2.get comparison.first =
                comparison.left.1.2.get comparison.first ∧
              ∀ side, side ≠ comparison.first →
                combined.1.2.get side =
                  comparison.right.1.2.get side

instance : Decidable LCellPhaseSplice := by
  unfold LCellPhaseSplice
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lCellPhaseSplice : LCellPhaseSplice := by
  native_decide

structure LEdgePhaseCase where
  leftType : OrthogonalCellType
  rightType : OrthogonalCellType
  leftInward : Side → Bool
  rightInward : Side → Bool
  side : Side
  deriving Fintype

/-- Whenever two legal local orientations assign complementary values to
matching colored half-edges, their supported L tables contain a pair of
exactly equal geometric port phases. -/
def LEdgePhaseMatchable : Prop :=
  ∀ edge : LEdgePhaseCase,
    PeriodicOrthogonalDrawing.satisfiesOrientation
        edge.leftType edge.leftInward →
      PeriodicOrthogonalDrawing.satisfiesOrientation
        edge.rightType edge.rightInward →
      edge.leftType.portColor edge.side =
        edge.rightType.portColor edge.side.opposite →
      (edge.leftType.portColor edge.side).isSome →
      edge.leftInward edge.side =
        !(edge.rightInward edge.side.opposite) →
        ∃ left right : LSupportedEntry,
          left.1.1 = edge.leftType ∧
            right.1.1 = edge.rightType ∧
            LEntryRealizes left.1 edge.leftInward ∧
            LEntryRealizes right.1 edge.rightInward ∧
              left.1.2.get edge.side =
                right.1.2.get edge.side.opposite

instance : Decidable LEdgePhaseMatchable := by
  unfold LEdgePhaseMatchable
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem lEdgePhaseMatchable : LEdgePhaseMatchable := by
  native_decide

end Gadget
end LeanTrominoes
