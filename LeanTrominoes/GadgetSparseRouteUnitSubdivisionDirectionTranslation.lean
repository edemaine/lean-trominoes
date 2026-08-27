/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation

/-! # Translation invariance of unit-subdivision direction words -/

namespace LeanTrominoes
namespace Gadget

open PeriodicOrthocrossing

/-- Translating every point of a polyline leaves its segment-major cardinal
direction word unchanged. -/
@[simp] theorem unitSubdivisionDirections_translatePolyline
    (offset : Cell) (points : List Cell) :
    unitSubdivisionDirections (translatePolyline offset points) =
      unitSubdivisionDirections points := by
  induction points using List.twoStepInduction with
  | nil => rfl
  | singleton point =>
      simp [translatePolyline, unitSubdivisionDirections]
  | cons_cons first second rest _ induction =>
      have tail := induction second
      simp only [translatePolyline, List.map_cons] at tail
      simp only [translatePolyline, List.map_cons,
        unitSubdivisionDirections]
      rw [AxisDirection.segmentLength_add_left,
        AxisDirection.between_add_left, tail]

end Gadget
end LeanTrominoes
