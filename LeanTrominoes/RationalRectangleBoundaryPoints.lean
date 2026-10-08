/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RationalAffineBoundaryContacts
import LeanTrominoes.RealRectangleBoundaryNoninterlacing

/-! # Rational coordinates of proper rectangle boundary ports -/
namespace LeanTrominoes.RationalAffineBoundary

def boundaryPoint (width height coordinate : ℚ) : Fin 4 → ℚ × ℚ
  | 0 => (0,coordinate)
  | 1 => (coordinate,height)
  | 2 => (width,coordinate)
  | _ => (coordinate,0)

theorem boundaryPoint_cast (width height coordinate : ℚ) (side : Fin 4) :
    (((boundaryPoint width height coordinate side).1 : ℝ),((boundaryPoint width height coordinate side).2 : ℝ)) =
      (RealRectangleBoundary.Port.mk side (coordinate : ℝ)).point (width : ℝ) (height : ℝ) := by
  fin_cases side <;> simp [boundaryPoint,RealRectangleBoundary.Port.point]

theorem boundaryPoint_on_boundary {width height coordinate : ℚ} (side : Fin 4)
    (inside : (RealRectangleBoundary.Port.mk side (coordinate : ℝ)).Inside (width : ℝ) (height : ℝ)) :
    let point := boundaryPoint width height coordinate side
    (((point.1 = 0 ∨ point.1 = width) ∧ 0 < point.2 ∧ point.2 < height) ∨
      ((point.2 = 0 ∨ point.2 = height) ∧ 0 < point.1 ∧ point.1 < width)) := by
  fin_cases side
  · have bounds : 0 < coordinate ∧ coordinate < height := by
      change (0 : ℝ) < (coordinate : ℝ) ∧ (coordinate : ℝ) < (height : ℝ) at inside
      exact_mod_cast inside
    exact Or.inl ⟨Or.inl rfl,bounds⟩
  · have bounds : 0 < coordinate ∧ coordinate < width := by
      change (0 : ℝ) < (coordinate : ℝ) ∧ (coordinate : ℝ) < (width : ℝ) at inside
      exact_mod_cast inside
    exact Or.inr ⟨Or.inr rfl,bounds⟩
  · have bounds : 0 < coordinate ∧ coordinate < height := by
      change (0 : ℝ) < (coordinate : ℝ) ∧ (coordinate : ℝ) < (height : ℝ) at inside
      exact_mod_cast inside
    exact Or.inl ⟨Or.inr rfl,bounds⟩
  · have bounds : 0 < coordinate ∧ coordinate < width := by
      change (0 : ℝ) < (coordinate : ℝ) ∧ (coordinate : ℝ) < (width : ℝ) at inside
      exact_mod_cast inside
    exact Or.inr ⟨Or.inl rfl,bounds⟩

theorem boundaryPoint_x_bounds {width height coordinate : ℚ} (widthPositive : 0 < width) (side : Fin 4)
    (inside : (RealRectangleBoundary.Port.mk side (coordinate : ℝ)).Inside (width : ℝ) (height : ℝ)) :
    0 ≤ (boundaryPoint width height coordinate side).1 ∧ (boundaryPoint width height coordinate side).1 ≤ width := by
  rcases boundaryPoint_on_boundary side inside with vertical | horizontal
  · rcases vertical.1 with equal | equal <;> rw [equal] <;> exact ⟨by linarith,by linarith⟩
  · exact ⟨horizontal.2.1.le,horizontal.2.2.le⟩

end LeanTrominoes.RationalAffineBoundary
