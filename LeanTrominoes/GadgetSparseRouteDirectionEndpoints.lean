/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.GadgetSparseRouteDirectionScalingCompiler
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # Endpoint projections of sparse route direction words -/

namespace LeanTrominoes.Gadget

/-- The first unit direction is the first geometric edge direction. -/
theorem unitSubdivisionDirections_headD
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (unitSubdivisionDirections points).headD .invalid =
      AxisDirection.polylineFirstDirection points := by
  cases points with
  | nil => simp [unitSubdivisionDirections, AxisDirection.polylineFirstDirection]
  | cons first rest =>
      cases rest with
      | nil => simp [unitSubdivisionDirections, AxisDirection.polylineFirstDirection]
      | cons second rest =>
          have positive := AxisDirection.segmentLength_positive_of_axisAligned
            (List.isChain_cons_cons.mp orthogonal).1
          obtain ⟨length, lengthEq⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt positive)
          simp [unitSubdivisionDirections, lengthEq, List.replicate_succ]

/-- Reversing a word exchanges endpoints and reverses their directions. -/
theorem reverseDirections_headD (directions : List AxisDirection) :
    (reverseDirections directions).headD .invalid =
      (directions.getLastD .invalid).opposite := by
  change (directions.reverse.map AxisDirection.opposite).headD
      AxisDirection.invalid.opposite = _
  rw [List.headD_map]
  simp

/-- The final unit direction is the final geometric edge direction. -/
theorem unitSubdivisionDirections_getLastD
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    (unitSubdivisionDirections points).getLastD .invalid =
      AxisDirection.polylineLastDirection points := by
  have first := unitSubdivisionDirections_headD points.reverse orthogonal.reverse
  rw [unitSubdivisionDirections_reverse points orthogonal,
    reverseDirections_headD] at first
  simpa [AxisDirection.polylineLastDirection] using
    congrArg AxisDirection.opposite first

/-- Repetition by a positive factor preserves the optional final direction. -/
theorem repeatDirections_getLast?
    (factor : Nat) (positive : 0 < factor) (directions : List AxisDirection) :
    (repeatDirections factor directions).getLast? = directions.getLast? := by
  induction directions using List.reverseRecOn with
  | nil => simp [repeatDirections]
  | append_singleton directions direction induction =>
      simp [repeatDirections, List.getLast?_replicate, Nat.ne_of_gt positive]

end LeanTrominoes.Gadget
