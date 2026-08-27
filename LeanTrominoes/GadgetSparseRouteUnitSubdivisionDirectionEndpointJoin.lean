/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionJoin
import LeanTrominoes.OrthogonalPolylineJoin

/-! # Direction words of nonempty endpoint joins -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- Joining any nonempty first polyline at its advertised endpoint
concatenates the two segment-major direction words. -/
theorem unitSubdivisionDirections_joinAtEndpoint
    {first second : List Cell}
    (firstNonempty : first ≠ [])
    (boundary : first.getLast? = second.head?) :
    unitSubdivisionDirections (LeanTrominoes.joinAtEndpoint first second) =
      unitSubdivisionDirections first ++
        unitSubdivisionDirections second := by
  cases first with
  | nil => exact (firstNonempty rfl).elim
  | cons first rest =>
      cases rest with
      | nil =>
          cases second with
          | nil => simp at boundary
          | cons secondHead secondTail =>
              have pointEq : first = secondHead := by
                simpa using boundary
              subst secondHead
              simp [LeanTrominoes.joinAtEndpoint,
                unitSubdivisionDirections]
      | cons next rest =>
          simpa [joinPolylines, LeanTrominoes.joinAtEndpoint] using
            unitSubdivisionDirections_joinPolylines
              (first := first :: next :: rest)
              (second := second) (by simp) boundary

end Gadget
end LeanTrominoes
