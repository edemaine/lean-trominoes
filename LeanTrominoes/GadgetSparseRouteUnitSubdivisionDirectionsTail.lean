/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionNormalization

/-! # Tails of unit-step route direction words -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- On a unit-step route, deleting its first point deletes exactly the first
direction token.  This is the bridge from full normalized-route direction
equalities to the inherited Figure Nine tail convention. -/
theorem unitSubdivisionDirections_tail_eq_tail_of_unitSteps
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionDirections points.tail =
      (unitSubdivisionDirections points).tail := by
  cases points with
  | nil => simp [unitSubdivisionDirections]
  | cons first rest =>
      cases rest with
      | nil => simp [unitSubdivisionDirections]
      | cons second rest =>
          have firstUnit : AxisDirection.IsUnitAxisStep first second :=
            (List.isChain_cons_cons.mp unitSteps).1
          simp [unitSubdivisionDirections,
            segmentLength_eq_one_of_unitAxisStep firstUnit]

end Gadget
end LeanTrominoes
