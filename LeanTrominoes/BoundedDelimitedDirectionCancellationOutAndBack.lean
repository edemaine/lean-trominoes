/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoundedDelimitedDirectionCancellationPolyline
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin

/-! # Direction decompositions for an out-and-back endpoint join -/

namespace LeanTrominoes
namespace BoundedDelimitedDirectionCancellation

/-- A unit-subdivision split `leading ++ path` separates the complete
direction word into the kept route through `path.head` and the path word. -/
theorem unitSubdivisionDirections_eq_kept_append_path
    (first leading path : List Cell)
    (firstOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline first)
    (pathNonempty : path ≠ [])
    (subdivision :
      AxisDirection.unitSubdividePolyline first = leading ++ path) :
    Gadget.unitSubdivisionDirections first =
      Gadget.unitSubdivisionDirections
          (leading ++ [path.head pathNonempty]) ++
        Gadget.unitSubdivisionDirections path := by
  let overlapHead := path.head pathNonempty
  let kept := leading ++ [overlapHead]
  have pathHead : path.head? = some overlapHead :=
    List.head?_eq_some_head pathNonempty
  have keptNonempty : kept ≠ [] := by simp [kept]
  have keptLast : kept.getLast? = some overlapHead := by
    simp [kept]
  have pointsEq : leading ++ path = joinAtEndpoint kept path := by
    unfold kept joinAtEndpoint overlapHead
    cases path with
    | nil => exact (pathNonempty rfl).elim
    | cons head tail => simp
  rw [← Gadget.unitSubdivisionDirections_unitSubdividePolyline
      first firstOrthogonal,
    subdivision, pointsEq,
    Gadget.unitSubdivisionDirections_joinAtEndpoint
      keptNonempty (by rw [keptLast, pathHead])]

/-- A split `path.reverse ++ rest` separates the suffix word into the
reversed path and the route continuing from `path.head`. -/
theorem unitSubdivisionDirections_eq_reverse_path_append_rest
    (second path rest : List Cell)
    (secondOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline second)
    (pathNonempty : path ≠ [])
    (subdivision :
      AxisDirection.unitSubdividePolyline second = path.reverse ++ rest) :
    Gadget.unitSubdivisionDirections second =
      Gadget.unitSubdivisionDirections path.reverse ++
        Gadget.unitSubdivisionDirections
          (path.head pathNonempty :: rest) := by
  let overlapHead := path.head pathNonempty
  let after := overlapHead :: rest
  have pathHead : path.head? = some overlapHead :=
    List.head?_eq_some_head pathNonempty
  have pathReverseNonempty : path.reverse ≠ [] := by
    simpa using pathNonempty
  have pathReverseLast : path.reverse.getLast? = some overlapHead := by
    rw [List.getLast?_reverse, pathHead]
  have afterHead : after.head? = some overlapHead := rfl
  have pointsEq :
      path.reverse ++ rest = joinAtEndpoint path.reverse after := by
    unfold after joinAtEndpoint
    simp
  rw [← Gadget.unitSubdivisionDirections_unitSubdividePolyline
      second secondOrthogonal,
    subdivision, pointsEq,
    Gadget.unitSubdivisionDirections_joinAtEndpoint
      pathReverseNonempty (by rw [pathReverseLast, afterHead])]

end BoundedDelimitedDirectionCancellation
end LeanTrominoes
