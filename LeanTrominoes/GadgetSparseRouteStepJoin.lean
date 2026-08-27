/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepGeometry
import LeanTrominoes.OrthogonalPolylineJoin

/-! # Exact route-step streams across endpoint joins -/

namespace LeanTrominoes
namespace Gadget

/-- Removing a duplicated common endpoint and joining two routes concatenates
their exact-offset streams, with no additional bridge offset. -/
theorem routeStepOffsets_joinAtEndpoint
    (first second : List Cell)
    (common : first.getLast? = second.head?) :
    routeStepOffsets (joinAtEndpoint first second) =
      routeStepOffsets first ++ routeStepOffsets second := by
  induction first using List.twoStepInduction generalizing second with
  | nil =>
      cases second <;>
        simp [joinAtEndpoint, routeStepOffsets] at common ⊢
  | singleton first =>
      cases second with
      | nil => simp at common
      | cons secondFirst secondRest =>
          have equal : first = secondFirst := by
            simpa using Option.some.inj common
          subst secondFirst
          simp [joinAtEndpoint, routeStepOffsets]
  | cons_cons first current rest _ induction =>
      have remainingCommon :
          (current :: rest).getLast? = second.head? := by
        simpa using common
      simp only [joinAtEndpoint, List.cons_append, routeStepOffsets]
      congr 1
      simpa only [joinAtEndpoint, List.cons_append] using
        induction current second remainingCommon

end Gadget
end LeanTrominoes
