/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.RetainedAngularFanFallbackRouteNormalizedDirections

/-! # Translation-free normalized fallback-suffix direction data -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Canonical loop-erased direction word of one complete fallback suffix,
represented at the origin. -/
def retainedNormalizedFallbackFanSuffixDirections
    (kind : RetainedFallbackFanKind)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (AxisDirection.normalizeOrthogonalPolyline
      (retainedFallbackFanSuffixRouteAt
        kind (0, 0) terminal slot))

/-- Absolute source coordinates disappear from the normalized fallback
suffix word just as they do from its raw direction word. -/
theorem retainedFallbackFanSuffixRouteAt_normalized_directions
    (kind : RetainedFallbackFanKind)
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (valid : kind.Valid terminal) :
    Gadget.unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline
          (retainedFallbackFanSuffixRouteAt
            kind center terminal slot)) =
      retainedNormalizedFallbackFanSuffixDirections
        kind terminal slot := by
  let zeroSuffix :=
    retainedFallbackFanSuffixRouteAt
      kind (0, 0) terminal slot
  have zeroSuffixHead :
      zeroSuffix.head? =
        some
          (retainedAngularFanOuterDemand
            (0, 0) terminal slot).gate := by
    exact retainedFallbackFanSuffixRouteAt_head?
      kind (0, 0) terminal slot
  have zeroSuffixNonempty : zeroSuffix ≠ [] := by
    intro empty
    rw [empty] at zeroSuffixHead
    simp at zeroSuffixHead
  have zeroSuffixOrthogonal : OrthogonalPolyline zeroSuffix :=
    retainedFallbackFanSuffixRouteAt_orthogonal
      kind (0, 0) terminal slot lengthPositive valid
  have translated :=
    retainedFallbackFanSuffixRouteAt_translatePolyline
      kind center (0, 0) terminal slot
  simp only [Cell.add_zero] at translated
  rw [← translated]
  unfold PeriodicOrthocrossing.translatePolyline
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
    zeroSuffixNonempty zeroSuffixOrthogonal center]
  unfold retainedNormalizedFallbackFanSuffixDirections
  exact Gadget.unitSubdivisionDirections_translatePolyline center _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
