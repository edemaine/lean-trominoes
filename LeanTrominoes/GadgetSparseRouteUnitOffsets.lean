/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteScaleTwelveSteps

/-! # Existing unit routes as subdivision-offset words -/

namespace LeanTrominoes
namespace Gadget

/-- A genuine unit axis step has Manhattan length one. -/
@[simp]
theorem segmentLength_eq_one_of_unitAxisStep
    {source target : Cell}
    (unit : AxisDirection.IsUnitAxisStep source target) :
    AxisDirection.segmentLength source target = 1 := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rcases source with ⟨sourceX, sourceY⟩
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.segmentLength,
      AxisDirection.step, Cell.add]

/-- On a route that is already unit-step, the segment-major subdivision word
is exactly its existing coordinate-offset word. -/
theorem unitSubdivisionOffsets_eq_routeStepOffsets
    (points : List Cell)
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    unitSubdivisionOffsets points = routeStepOffsets points := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [unitSubdivisionOffsets, routeStepOffsets]
  | cons_cons first second rest _ induction =>
      have firstUnit : AxisDirection.IsUnitAxisStep first second :=
        (List.isChain_cons_cons.mp unitSteps).1
      have remainingUnitSteps :
          (second :: rest).IsChain AxisDirection.IsUnitAxisStep :=
        (List.isChain_cons_cons.mp unitSteps).2
      simp only [unitSubdivisionOffsets, routeStepOffsets,
        segmentLength_eq_one_of_unitAxisStep firstUnit,
        List.replicate_one, List.singleton_append]
      rw [stepOffset_eq_between_step_of_unitAxisStep firstUnit]
      rw [induction second remainingUnitSteps]

end Gadget
end LeanTrominoes
