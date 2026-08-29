/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixRayDirectionSemantics
import LeanTrominoes.RetainedAngularFanOuterRadialPrefixes

/-! # Direction semantics of exterior fallback radial prefixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

/-- The ordinary radial prefix consists of its finite lane shift followed
by every inward primitive block except the final one. -/
theorem retainedTerminalFanOuterRadialPrefix_directions
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    Gadget.unitSubdivisionDirections
        (retainedTerminalFanOuterRadialPrefix center terminal slot) =
      prefixDirections .ordinary terminal.1 slot ++
        radialCopies
          (retainedTerminalFanOuterRadialLength terminal - 1)
          terminal.1 := by
  unfold retainedTerminalFanOuterRadialPrefix
  dsimp only
  rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
  · unfold prefixDirections retainedTerminalFanOuterLaneShiftRouteAt
    rw [Gadget.unitSubdivisionDirections_translatePolyline]
    change _ ++
        Gadget.unitSubdivisionDirections
          ((retainedTerminalFanOuterInwardRayOfLength terminal.1
            (retainedTerminalFanOuterRadialLength terminal - 1)).rasterize
              _) = _
    rw [retainedTerminalFanOuterInwardRayOfLength_directions]
  · intro empty
    have head := retainedTerminalFanOuterLaneShiftRouteAt_head?
      (retainedAngularFanOuterDemand center terminal slot).gate
      terminal.1 slot
    simp [empty] at head
  · rw [retainedTerminalFanOuterLaneShiftRouteAt_getLast?,
      RetainedRay.rasterize_head?]

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
