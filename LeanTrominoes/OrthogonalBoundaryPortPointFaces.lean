/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcRouting

/-! # Proper integral rectangle ports identify their unique boundary face -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

theorem Port.point_bounds_faces {width height margin : Int}
    (widthPositive : 0 < width) (heightPositive : 0 < height) (marginNonnegative : 0 ≤ margin)
    {port : Port} (inside : port.Inside width height margin) :
    (0 ≤ (port.point width height).1 ∧ (port.point width height).1 ≤ width) ∧
    (0 ≤ (port.point width height).2 ∧ (port.point width height).2 ≤ height) ∧
    ((port.point width height).1 = 0 ↔ port.side.val = 0) ∧
    ((port.point width height).1 = width ↔ port.side.val = 2) ∧
    ((port.point width height).2 = 0 ↔ port.side.val = 3) ∧
    ((port.point width height).2 = height ↔ port.side.val = 1) := by
  rcases port with ⟨side,coordinate⟩
  fin_cases side <;> simp [Port.point,Port.Inside] at inside ⊢ <;> omega

end LeanTrominoes.OrthogonalBoundaryRouting
