/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition

/-! # Direction words of retained fallback source prefixes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Deleting the old endpoint before the fixed terminal-fan refinement
deletes its complete incident segment.  The surviving direction word is
then the fixed-copy expansion of the unscaled source prefix. -/
theorem retainedFallbackSourcePrefix_directions
    (route : List Cell) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix route) =
      Gadget.repeatDirections retainedTerminalFanTotalRefinement
        (Gadget.unitSubdivisionDirections route.dropLast) := by
  unfold retainedFallbackSourcePrefix
  rw [scalePolyline_dropLast_eq]
  exact Gadget.unitSubdivisionDirections_scalePolyline
    retainedTerminalFanTotalRefinement (by native_decide) route.dropLast

/-- If the source route was already positively scaled, the two fixed-copy
expansions combine into one product factor on the original source prefix. -/
theorem retainedFallbackSourcePrefix_scaled_directions
    (factor : Nat)
    (positive : 0 < factor)
    (route : List Cell) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix
          (scalePolyline factor route)) =
      Gadget.repeatDirections
        (retainedTerminalFanTotalRefinement * factor)
        (Gadget.unitSubdivisionDirections route.dropLast) := by
  rw [retainedFallbackSourcePrefix_directions,
    scalePolyline_dropLast_eq,
    Gadget.unitSubdivisionDirections_scalePolyline factor positive,
    Gadget.repeatDirections_repeatDirections]

/-- The actual final fallback source prefix is a 1152-fold expansion of
the raw retained carrier-or-bend route with its last segment removed. -/
theorem retainedFallbackSourcePrefix_sourceClearanceScaled_directions
    (route : List Cell) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix
          (scalePolyline retainedAngularFanSourceClearanceFactor route)) =
      Gadget.repeatDirections 1152
        (Gadget.unitSubdivisionDirections route.dropLast) := by
  simpa using retainedFallbackSourcePrefix_scaled_directions
    retainedAngularFanSourceClearanceFactor
    retainedAngularFanSourceClearanceFactor_pos route

end PeriodicEightOccurrenceSplit
end LeanTrominoes
