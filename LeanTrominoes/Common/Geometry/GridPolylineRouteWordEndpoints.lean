/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRouteWord

/-! # Executable route words preserve their first and last endpoints -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem joinWord_endpoints {first : List Cell} {rest : List (List Cell)}
    (long : ∀ piece ∈ first :: rest, 2 ≤ piece.length) :
    2 ≤ (joinWord (first :: rest)).length ∧
      (joinWord (first :: rest)).head? = first.head? ∧
      (joinWord (first :: rest)).getLast? = (first :: rest).getLast?.bind List.getLast? := by
  induction rest generalizing first with
  | nil => exact ⟨long first (by simp),rfl,by simp [joinWord]⟩
  | cons next rest ih =>
    have firstLong := long first (by simp)
    have tail := ih (fun piece member => long piece (List.mem_cons_of_mem first member))
    change 2 ≤ (joinPolylines first (joinWord (next :: rest))).length ∧ _
    refine ⟨?_,joinPolylines_head?_of_first (by intro empty; simp [empty] at firstLong),?_⟩
    · unfold joinPolylines
      simp only [List.length_append]
      omega
    · change (joinPolylines first (joinWord (next :: rest))).getLast? = _
      rw [joinPolylines_getLast?_of_second tail.1,tail.2.2,List.getLast?_cons_cons]

end LeanTrominoes.GridPolyline
