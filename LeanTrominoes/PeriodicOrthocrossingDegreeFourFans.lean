/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealBoxIntersection
import LeanTrominoes.PeriodicGridDrawingRealGeometry
import Mathlib.Tactic.FinCases

/-! # Four orthogonal ports in a vertex block

The fourth route initially leaves south and then reaches the rightmost
port. Every closed contact between distinct fan routes is at the center.
-/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def degreeFourFan (rank : Fin 4) : List Cell :=
  match rank.val with
  | 0 => [(0,2),(-1,2),(-1,3)]
  | 1 => [(0,2),(0,3)]
  | 2 => [(0,2),(1,2),(1,3)]
  | _ => [(0,2),(0,1),(2,1),(2,3)]

theorem degreeFourFan_endpoints (rank : Fin 4) :
    (degreeFourFan rank).head? = some (0,2) ∧
      (degreeFourFan rank).getLast? = some ((rank.val : Int)-1,3) := by
  fin_cases rank <;> decide +kernel

theorem degreeFourFan_orthogonal (rank : Fin 4) :
    ∀ segment ∈ gridPolylineSegments (degreeFourFan rank), segment.IsAxisAligned := by
  fin_cases rank <;> decide +kernel

theorem degreeFourFan_bounded (rank : Fin 4) :
    ∀ segment ∈ gridPolylineSegments (degreeFourFan rank),
      -1 ≤ segment.start.1 ∧ segment.start.1 ≤ 2 ∧ 1 ≤ segment.start.2 ∧ segment.start.2 ≤ 3 ∧
      -1 ≤ segment.finish.1 ∧ segment.finish.1 ≤ 2 ∧ 1 ≤ segment.finish.2 ∧ segment.finish.2 ≤ 3 := by
  fin_cases rank <;> decide +kernel

theorem degreeFourFan_box_certificate :
    ∀ first second : Fin 4, first ≠ second →
      ∀ a ∈ gridPolylineSegments (degreeFourFan first),
        ∀ b ∈ gridPolylineSegments (degreeFourFan second),
          GridSegment.BoxIntersectionIsPoint a b (0,2) := by
  decide +kernel

theorem degreeFourFan_meet_only_at_center {first second : Fin 4} (different : first ≠ second)
    {point : ℝ × ℝ} (firstMember : GridPolyline.RealContains (degreeFourFan first) point)
    (secondMember : GridPolyline.RealContains (degreeFourFan second) point) : point = (0,2) := by
  obtain ⟨a,am,ap⟩ := firstMember
  obtain ⟨b,bm,bp⟩ := secondMember
  simpa using GridSegment.real_intersection_eq_of_box_certificate
    (degreeFourFan_box_certificate first second different a am b bm) ap bp

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
