/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentKickedCoreDigitalRoutes

/-! # Linear spacing factors for the cubic refinement construction

These factors satisfy the separation, direction-perturbation, and digital
slope estimates. Their product times the original period has a uniform
cubic bound. This file proves the estimates, not the drawing construction.
-/
namespace LeanTrominoes.OrthogonalDrawingRefinement.Cubic

def coreFactor (gridSize : Nat) : Nat := 160*gridSize+1600
def rasterFactor (gridSize : Nat) : Nat := 16*gridSize+32
def refinementFactor (gridSize : Nat) : Nat := coreFactor gridSize*rasterFactor gridSize

theorem coreFactor_positive (gridSize : Nat) : 0 < coreFactor gridSize := by
  unfold coreFactor
  omega

theorem rasterFactor_positive (gridSize : Nat) : 0 < rasterFactor gridSize := by
  unfold rasterFactor
  omega

theorem coreFactor_tube_spacing (gridSize : Nat) :
    4*(2*(gridSize : Int))*(10+3) < (coreFactor gridSize : Int) := by
  simp only [coreFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem coreFactor_cross_spacing (gridSize : Nat) :
    4*(2*(gridSize : Int))*20+2*20*20+1 < (coreFactor gridSize : Int) := by
  simp only [coreFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem coreFactor_slope_spacing (gridSize : Nat) : 4*10 < (coreFactor gridSize : Int) := by
  simp only [coreFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem rasterFactor_slope_spacing (gridSize : Nat) :
    3*((4*(gridSize : Int)+1)+1) < (rasterFactor gridSize : Int) := by
  simp only [rasterFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem refined_period_le_cubic {gridSize : Nat} (positive : 0 < gridSize) :
    refinementFactor gridSize*gridSize ≤ 84480*gridSize^3 := by
  have square : gridSize ≤ gridSize*gridSize := by nlinarith
  have cube := Nat.mul_le_mul_left gridSize square
  calc
    refinementFactor gridSize*gridSize =
        2560*gridSize^3+30720*gridSize^2+51200*gridSize := by
      unfold refinementFactor coreFactor rasterFactor
      ring
    _ ≤ 84480*gridSize^3 := by nlinarith

end LeanTrominoes.OrthogonalDrawingRefinement.Cubic
