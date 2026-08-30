/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierIndexedRouteEvidence

/-! # Compact normalization requests at indexed final carriers -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Package an indexed occurrence's named evidence and semantic address into
the compact request consumed by directional extensionality. -/
theorem FinalCarrierIndexedOccurrence.normalizationRequest
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalCarrierIndexedOccurrence Variable)
    (nextSlice : Bool)
    (spanLarge :
      8 ≤ (finalCarrierRouteGeometryAt occurrence.source
        occurrence.taggedLink nextSlice).span) :
    occurrence.NormalizationRequest nextSlice := by
  apply occurrence.withScaledRouteEvidence
  intro evidence
  exact ⟨spanLarge, evidence⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
