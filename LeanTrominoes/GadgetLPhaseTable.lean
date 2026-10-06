/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetPortRefinement
import LeanTrominoes.GadgetSupportedPortTable

/-!
# Verified geometric phase laws for the Figure 11 L gadgets

Boolean port values forget which supported geometric boundary state crosses
an interface.  Exhaustive kernel-checked certificates in this file establish the
closure properties needed to recover those phases globally: route-end phases
can be recombined, one side of any local state can be spliced independently,
and complementary same-color half-edges always admit matching exact ports.
-/

namespace LeanTrominoes
namespace Gadget

set_option synthInstance.maxSize 65536

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
private theorem lRoutingPhaseRectangular_fiber :
    ∀ cellType first second,
      cellType.routingSides = some (first, second) →
        ∀ inward (left right : LSupportedConfiguration cellType),
          LEntryRealizes (cellType, left.val) inward →
          LEntryRealizes (cellType, right.val) inward →
            ∃ combined : LSupportedConfiguration cellType,
              LEntryRealizes (cellType, combined.val) inward ∧
                combined.val.get first = left.val.get first ∧
                combined.val.get second = right.val.get second := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lRoutingPhaseRectangular : LRoutingPhaseRectangular := by
  intro comparison routing leftType rightType leftReal rightReal
  have leftPair : comparison.left.val =
      (comparison.cellType, comparison.left.val.2) := Prod.ext leftType rfl
  have rightPair : comparison.right.val =
      (comparison.cellType, comparison.right.val.2) := Prod.ext rightType rfl
  have leftMember := comparison.left.property
  have rightMember := comparison.right.property
  rw [leftPair] at leftMember leftReal
  rw [rightPair] at rightMember rightReal
  let left : LSupportedConfiguration comparison.cellType :=
    ⟨comparison.left.val.2, leftMember⟩
  let right : LSupportedConfiguration comparison.cellType :=
    ⟨comparison.right.val.2, rightMember⟩
  obtain ⟨combined, realizes, first, second⟩ :=
    lRoutingPhaseRectangular_fiber comparison.cellType comparison.first
      comparison.second routing comparison.inward left right leftReal rightReal
  exact ⟨⟨(comparison.cellType, combined.val), combined.property⟩,
    rfl, realizes, first, second⟩

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
private theorem lCellPhaseSplice_fiber :
    ∀ cellType first inward (left right : LSupportedConfiguration cellType),
      LEntryRealizes (cellType, left.val) inward →
      LEntryRealizes (cellType, right.val) inward →
        ∃ combined : LSupportedConfiguration cellType,
          LEntryRealizes (cellType, combined.val) inward ∧
            combined.val.get first = left.val.get first ∧
              ∀ side, side ≠ first → combined.val.get side = right.val.get side := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lCellPhaseSplice : LCellPhaseSplice := by
  intro comparison leftType rightType leftReal rightReal
  have leftPair : comparison.left.val =
      (comparison.cellType, comparison.left.val.2) := Prod.ext leftType rfl
  have rightPair : comparison.right.val =
      (comparison.cellType, comparison.right.val.2) := Prod.ext rightType rfl
  have leftMember := comparison.left.property
  have rightMember := comparison.right.property
  rw [leftPair] at leftMember leftReal
  rw [rightPair] at rightMember rightReal
  let left : LSupportedConfiguration comparison.cellType :=
    ⟨comparison.left.val.2, leftMember⟩
  let right : LSupportedConfiguration comparison.cellType :=
    ⟨comparison.right.val.2, rightMember⟩
  obtain ⟨combined, realizes, first, other⟩ :=
    lCellPhaseSplice_fiber comparison.cellType comparison.first comparison.inward
      left right leftReal rightReal
  exact ⟨⟨(comparison.cellType, combined.val), combined.property⟩,
    rfl, realizes, first, other⟩

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
private theorem lEdgePhaseMatchable_fiber :
    ∀ leftType leftInward,
      PeriodicOrthogonalDrawing.satisfiesOrientation leftType leftInward →
        ∀ rightType side,
          leftType.portColor side = rightType.portColor side.opposite →
          (leftType.portColor side).isSome →
            ∀ rightInward,
              PeriodicOrthogonalDrawing.satisfiesOrientation rightType rightInward →
              leftInward side = !(rightInward side.opposite) →
                ∃ (left : LSupportedConfiguration leftType)
                  (right : LSupportedConfiguration rightType),
                  LEntryRealizes (leftType, left.val) leftInward ∧
                    LEntryRealizes (rightType, right.val) rightInward ∧
                      left.val.get side = right.val.get side.opposite := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem lEdgePhaseMatchable : LEdgePhaseMatchable := by
  intro edge leftValid rightValid colorEq active complementary
  obtain ⟨left, right, leftReal, rightReal, portsEq⟩ :=
    lEdgePhaseMatchable_fiber edge.leftType edge.leftInward leftValid
      edge.rightType edge.side colorEq active edge.rightInward rightValid complementary
  exact ⟨⟨(edge.leftType, left.val), left.property⟩,
    ⟨(edge.rightType, right.val), right.property⟩,
    rfl, rfl, leftReal, rightReal, portsEq⟩

end Gadget
end LeanTrominoes
