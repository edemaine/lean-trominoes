/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin

/-! # Direction words after localized route normalization -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- If route normalization is already known to normalize a prefix and
reattach a simple orthogonal tail by unit subdivision, its direction word is
the concatenation of the normalized-prefix word and the original tail word.
-/
theorem unitSubdivisionDirections_normalized_join
    {route finitePrefix tail : List Cell}
    {boundary : Cell}
    (normalizedEq :
      AxisDirection.normalizeOrthogonalPolyline route =
        joinAtEndpoint
          (AxisDirection.normalizeOrthogonalPolyline finitePrefix)
          (AxisDirection.unitSubdividePolyline tail))
    (prefixNonempty : finitePrefix ≠ [])
    (prefixOrthogonal : OrthogonalPolyline finitePrefix)
    (prefixLast : finitePrefix.getLast? = some boundary)
    (tailNonempty : tail ≠ [])
    (tailOrthogonal : OrthogonalPolyline tail)
    (tailHead : tail.head? = some boundary) :
    unitSubdivisionDirections
        (AxisDirection.normalizeOrthogonalPolyline route) =
      unitSubdivisionDirections
          (AxisDirection.normalizeOrthogonalPolyline finitePrefix) ++
        unitSubdivisionDirections tail := by
  have normalizedPrefixNonempty :
      AxisDirection.normalizeOrthogonalPolyline finitePrefix ≠ [] :=
    AxisDirection.normalizeOrthogonalPolyline_ne_nil
      prefixNonempty prefixOrthogonal
  have normalizedPrefixLast :
      (AxisDirection.normalizeOrthogonalPolyline finitePrefix).getLast? =
        some boundary := by
    rw [AxisDirection.normalizeOrthogonalPolyline_getLast?
      prefixNonempty prefixOrthogonal, prefixLast]
  have subdividedTailHead :
      (AxisDirection.unitSubdividePolyline tail).head? =
        some boundary := by
    rw [AxisDirection.unitSubdividePolyline_head?
      tailNonempty, tailHead]
  rw [normalizedEq]
  rw [unitSubdivisionDirections_joinAtEndpoint
    normalizedPrefixNonempty
    (normalizedPrefixLast.trans subdividedTailHead.symm)]
  rw [unitSubdivisionDirections_unitSubdividePolyline
    tail tailOrthogonal]

end Gadget
end LeanTrominoes
