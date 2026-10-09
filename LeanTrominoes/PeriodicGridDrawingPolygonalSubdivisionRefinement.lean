/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionPlanarity
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionLocality
import LeanTrominoes.PeriodicGridDrawingStraightRefinementTheorem

/-! # Polynomial orthogonal refinement of the polygonal bend subdivision -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open OrthogonalDrawingRefinement

def bendRefinementFactor (drawing : PeriodicGridDrawing) : Nat := 32*drawing.gridSize+32

theorem bendRefinementFactor_spacing (drawing : PeriodicGridDrawing) :
    16*(drawing.gridSize:Int)+8 < (bendRefinementFactor drawing:Int) := by
  simp only [bendRefinementFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have positive : (0:Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  omega

def orthogonalSubdivision {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing :=
  straightRefinementDrawing (subdivisionGraph source drawing (bendRefinementFactor drawing))
    (subdivisionDrawing source drawing (bendRefinementFactor drawing))

theorem orthogonalSubdivision_planar {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) (degree : source.DegreeAtMost 4) :
    (orthogonalSubdivision source drawing).IsRealPlanarDrawing
      (subdivisionGraph source drawing (bendRefinementFactor drawing)) := by
  have spacing := bendRefinementFactor_spacing drawing
  exact straightRefinementDrawing_isRealPlanarDrawing
    (subdivisionDrawing_planar planar localDrawing localGraph spacing)
    (subdivisionGraph_degreeAtMost degree (by omega) drawing _)
    (subdivisionGraph_local planar localDrawing localGraph (by have := Nat.zero_lt_succ drawing.gridSizePred; omega))
    (fun _ member => subdivisionDrawing_straight source drawing _ member)

theorem orthogonalSubdivision_local {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) (degree : source.DegreeAtMost 4) :
    (orthogonalSubdivision source drawing).IsRealLocal
      (subdivisionGraph source drawing (bendRefinementFactor drawing)) := by
  have spacing := bendRefinementFactor_spacing drawing
  exact straightRefinementDrawing_isRealLocal
    (subdivisionDrawing_planar planar localDrawing localGraph spacing)
    (subdivisionGraph_degreeAtMost degree (by omega) drawing _)
    (subdivisionGraph_local planar localDrawing localGraph (by have := Nat.zero_lt_succ drawing.gridSizePred; omega))
    (fun _ member => subdivisionDrawing_straight source drawing _ member)

theorem orthogonalSubdivision_orthogonal {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source) (localDrawing : drawing.IsRealLocal source)
    (localGraph : source.IsLocal) (degree : source.DegreeAtMost 4) :
    (orthogonalSubdivision source drawing).IsOrthogonal := by
  have spacing := bendRefinementFactor_spacing drawing
  exact straightRefinementDrawing_orthogonal
    (subdivisionDrawing_planar planar localDrawing localGraph spacing)
    (subdivisionGraph_degreeAtMost degree (by omega) drawing _)
    (subdivisionGraph_local planar localDrawing localGraph (by have := Nat.zero_lt_succ drawing.gridSizePred; omega))
    (fun _ member => subdivisionDrawing_straight source drawing _ member)

theorem orthogonalSubdivision_gridSize_bound {V : Type*} [DecidableEq V]
    (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (orthogonalSubdivision source drawing).gridSize ≤ 865075200*drawing.gridSize^6 := by
  have positive : 0 < bendRefinementFactor drawing := by unfold bendRefinementFactor; omega
  have gridPositive : 1 ≤ drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
  have factorBound : bendRefinementFactor drawing ≤ 64*drawing.gridSize := by unfold bendRefinementFactor; omega
  have periodBound : bendRefinementFactor drawing*drawing.gridSize ≤ 64*drawing.gridSize^2 := by
    simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul_right drawing.gridSize factorBound
  have cubic := Nat.pow_le_pow_left periodBound 3
  have bound := straightRefinementDrawing_gridSize_cubic
    (graph := subdivisionGraph source drawing (bendRefinementFactor drawing))
    (drawing := subdivisionDrawing source drawing (bendRefinementFactor drawing))
  rw [subdivisionDrawing_gridSize source drawing positive] at bound
  change (orthogonalSubdivision source drawing).gridSize ≤ _ at bound
  calc
    (orthogonalSubdivision source drawing).gridSize ≤ 3300*(bendRefinementFactor drawing*drawing.gridSize)^3 := bound
    _ ≤ 3300*(64*drawing.gridSize^2)^3 := Nat.mul_le_mul_left 3300 cubic
    _ = 865075200*drawing.gridSize^6 := by ring

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
