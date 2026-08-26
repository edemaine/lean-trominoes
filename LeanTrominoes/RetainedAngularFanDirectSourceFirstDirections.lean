/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineEndpointDirectionTranslation
import LeanTrominoes.RetainedAngularFanDirectSourceRouteChoice

/-! # Clause-side ordering of coordinated direct-source routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Finite lookup table for the clause-side direction of one coordinated
direct-source atlas entry. -/
def retainedDirectSourceCoordinatedFirstDirection
    (kind : RetainedDirectClauseKind)
    (index : Fin (retainedDirectSourcePrefixChoices kind).length) :
    AxisDirection :=
  AxisDirection.polylineFirstDirection
    (retainedDirectSourceFanCompleteRouteAt kind index ⟨0, by decide⟩)

/-- The clause-side direction of a coordinated direct-source route depends
only on its finite atlas entry, not on its variable-side occurrence slot. -/
theorem retainedDirectSourceFanCompleteRouteAt_firstDirection_eq :
    ∀ (kind : RetainedDirectClauseKind)
      (index : Fin (retainedDirectSourcePrefixChoices kind).length)
      (slot : RetainedTerminalSlot),
      AxisDirection.polylineFirstDirection
          (retainedDirectSourceFanCompleteRouteAt kind index slot) =
        retainedDirectSourceCoordinatedFirstDirection kind index := by
  native_decide

end PeriodicEightOccurrenceSplit
end LeanTrominoes
