/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetIPortRefinement

/-!
# Verified geometric phase laws for the Figure 12 I gadgets

Straight vertical I-gadget wires admit one extra neutral local phase.  The
other local states, and the visibly directed phase of a vertical wire,
determine their exact ports from the Boolean orientation.  This file filters
out that optional neutral vertical phase and certifies that the remaining
preferred states are locally complete and match across every oriented edge.
-/

namespace LeanTrominoes
namespace Gadget

/-- A viable separated-table entry realizes the requested Boolean values on
every colored side of its cell. -/
def IEntryRealizes
    (entry : OrthogonalCellType × PortConfiguration)
    (inward : Side → Bool) : Prop :=
  ∀ side, (entry.1.portColor side).isSome →
    iConfigurationInward entry.1 entry.2 side = inward side

instance (entry : OrthogonalCellType × PortConfiguration)
    (inward : Side → Bool) : Decidable (IEntryRealizes entry inward) := by
  unfold IEntryRealizes
  infer_instance

/-- The optional ambiguity occurs only for straight vertical wires.  Retain
the phase whose colored marker visibly specifies both active directions. -/
def IEntryPreferred
    (entry : OrthogonalCellType × PortConfiguration) : Prop :=
  match entry.1 with
  | .wire .vertical _ =>
      ∀ side color, entry.1.portColor side = some color →
        iPortSpecifiedInward color side (entry.2.get side) =
          some (iConfigurationInward entry.1 entry.2 side)
  | _ => True

instance (entry : OrthogonalCellType × PortConfiguration) :
    Decidable (IEntryPreferred entry) := by
  unfold IEntryPreferred
  split
  · infer_instance
  · infer_instance

/-- Viable Figure 12 states with the redundant neutral vertical-wire phase
removed. -/
def iPreferredCellPortTable :
    Finset (OrthogonalCellType × PortConfiguration) :=
  iSeparatedCellPortTable.filter IEntryPreferred

abbrev IPreferredEntry :=
  { entry // entry ∈ iPreferredCellPortTable }

/-- Every satisfying Boolean orientation is represented by a preferred
Figure 12 state. -/
def IPreferredOrientationComplete : Prop :=
  ITableOrientationComplete iPreferredCellPortTable

/-- Preferred states with matching colors and opposite Boolean directions
have exactly equal geometric port footprints. -/
def IPreferredPortsMatch : Prop :=
  ∀ left right : IPreferredEntry,
    ∀ side color,
      left.1.1.portColor side = some color →
      right.1.1.portColor side.opposite = some color →
      iConfigurationInward left.1.1 left.1.2 side =
          !(iConfigurationInward right.1.1 right.1.2 side.opposite) →
        left.1.2.get side = right.1.2.get side.opposite

instance : Decidable IPreferredOrientationComplete := by
  unfold IPreferredOrientationComplete
  infer_instance

instance : Decidable IPreferredPortsMatch := by
  unfold IPreferredPortsMatch
  infer_instance

/-- The two finite phase facts needed for the global Figure 12 lift. -/
def IPreferredPhaseTableCorrect : Prop :=
  IPreferredOrientationComplete ∧ IPreferredPortsMatch

instance : Decidable IPreferredPhaseTableCorrect := by
  unfold IPreferredPhaseTableCorrect
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Exhaustive certificate for the preferred Figure 12 phase table. -/
theorem iPreferredPhaseTableCorrect : IPreferredPhaseTableCorrect := by
  native_decide

end Gadget
end LeanTrominoes
