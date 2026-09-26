/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnitRouteEndpointDisplacement
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionSteps
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionReversal

/-! # Recovering translated endpoints from arbitrary orthogonal route words -/
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Gadget PeriodicOrthocrossing

theorem displacement_orthogonalRoute (horizontal : Bool) (points : List Cell) (first last : Cell)
    (head : points.head? = some first) (tail : points.getLast? = some last)
    (orthogonal : OrthogonalPolyline points) :
    displacement horizontal (Gadget.unitSubdivisionDirections points) =
      component horizontal last - component horizontal first := by
  have nonempty : points ≠ [] := by intro h; simp [h] at head
  have h := displacement_unitSubdivisionDirections horizontal (AxisDirection.unitSubdividePolyline points) first last
    (by rw [AxisDirection.unitSubdividePolyline_head? nonempty,head])
    (by rw [AxisDirection.unitSubdividePolyline_getLast? nonempty orthogonal,tail])
    (AxisDirection.unitSubdividePolyline_unitSteps orthogonal)
  rw [Gadget.unitSubdivisionDirections_unitSubdividePolyline points orthogonal] at h
  exact h

theorem translatedEndpoint_offset (horizontal : Bool) (period : Nat) (hp : 0 < period)
    (points : List Cell) (first target offset : Cell)
    (head : points.head? = some first)
    (tail : points.getLast? = some (Cell.add target (Cell.scale period offset)))
    (orthogonal : OrthogonalPolyline points)
    (inside : 0 ≤ component horizontal target ∧ component horizontal target < (period:Int)) :
    (component horizontal first + displacement horizontal (Gadget.unitSubdivisionDirections points))/(period:Int) =
      component horizontal offset := by
  rw [displacement_orthogonalRoute horizontal points first _ head tail orthogonal]
  have endComponent : component horizontal (Cell.add target (Cell.scale period offset)) =
      component horizontal target + (period:Int)*component horizontal offset := by
    cases horizontal <;> rfl
  rw [endComponent]
  have cancel : component horizontal first +
      (component horizontal target + (period:Int)*component horizontal offset - component horizontal first) =
      component horizontal target + (period:Int)*component horizontal offset := by omega
  rw [cancel,Int.add_mul_ediv_left _ _ (by omega),Int.ediv_eq_zero_of_lt inside.1 inside.2]
  simp


theorem translatedEndpoint_position (horizontal : Bool) (period : Nat)
    (points : List Cell) (first target offset : Cell)
    (head : points.head? = some first)
    (tail : points.getLast? = some (Cell.add target (Cell.scale period offset)))
    (orthogonal : OrthogonalPolyline points)
    (inside : 0 ≤ component horizontal target ∧ component horizontal target < (period:Int)) :
    (component horizontal first + displacement horizontal (Gadget.unitSubdivisionDirections points))%(period:Int) =
      component horizontal target := by
  rw [displacement_orthogonalRoute horizontal points first _ head tail orthogonal]
  have endComponent : component horizontal (Cell.add target (Cell.scale period offset)) =
      component horizontal target + (period:Int)*component horizontal offset := by
    cases horizontal <;> rfl
  rw [endComponent]
  have cancel : component horizontal first +
      (component horizontal target + (period:Int)*component horizontal offset - component horizontal first) =
      component horizontal target + (period:Int)*component horizontal offset := by omega
  rw [cancel,Int.add_mul_emod_self_left,Int.emod_eq_of_lt inside.1 inside.2]

end LeanTrominoes.DelimitedDirectionDisplacement
