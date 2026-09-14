/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCoRE
import LeanTrominoes.CompletionLHardness
import LeanTrominoes.CompletionIHardness

/-! # Co-r.e. completeness of periodic tromino completion in the plane

The input specifies prescribed trominoes by a finite motif and two independent
integer periods. A completing plane tiling can be arbitrary. Both the straight
and the right-angle tromino give co-r.e.-complete completion problems.
-/

namespace LeanTrominoes.PeriodicTrominoPrefill

theorem planeProblem_coREHard (t : Tromino) : LeanWang.CoREHard (planeProblem t) := by
  cases t
  · exact CompletionPattern.IBricks.iCompletion_coREHard
  · exact CompletionPattern.LBricks.lCompletion_coREHard

/-- Periodic plane completion is co-r.e.-complete for either tromino. -/
theorem planeProblem_coREComplete (t : Tromino) : LeanWang.CoREComplete (planeProblem t) :=
  ⟨planeProblem_coRE t,planeProblem_coREHard t⟩

end LeanTrominoes.PeriodicTrominoPrefill
