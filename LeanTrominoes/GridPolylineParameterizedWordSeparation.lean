/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRouteWord
import Mathlib.Data.Rat.Defs

/-! # Parameter-ordered endpoint contacts give a geometrically separated route word -/
namespace LeanTrominoes.GridPolyline

theorem separatedWord_of_parameter_order {Piece : Type*} (pieces : List Piece)
    (route : Piece → List Cell) (start finish : Piece → ℚ)
    (positive : ∀ piece ∈ pieces, start piece < finish piece)
    (ordered : pieces.Pairwise (fun first last => finish first ≤ start last))
    (contacts : ∀ first ∈ pieces, ∀ last ∈ pieces, finish first ≤ start last → ∀ point,
      RealContains (route first) point → RealContains (route last) point →
      finish first = start last ∧ point = realCell ((route first).getLast?.getD (0,0))) :
    SeparatedWord (pieces.map route) := by
  induction pieces with
  | nil => trivial
  | cons first rest ih =>
    cases rest with
    | nil => trivial
    | cons next later =>
      have order := List.pairwise_cons.mp ordered
      have nextOrder := List.pairwise_cons.mp order.2
      have nextPositive := positive next (by simp)
      simp only [List.map_cons]
      change (∀ point, RealContains (route first) point → RealContains (route next) point →
          point = realCell ((route first).getLast?.getD (0,0))) ∧
        (∀ laterRoute ∈ later.map route, ∀ point, RealContains (route first) point → RealContains laterRoute point → False) ∧
        SeparatedWord ((next :: later).map route)
      refine ⟨?_,?_,ih (fun piece member => positive piece (List.mem_cons_of_mem first member)) order.2 ?_⟩
      · intro point firstContains nextContains
        exact (contacts first (by simp) next (by simp) (order.1 next (by simp)) point firstContains nextContains).2
      · intro laterRoute member point firstContains laterContains
        obtain ⟨last,lastMember,rfl⟩ := List.mem_map.mp member
        have firstBefore := order.1 next (by simp)
        have lastAfter := nextOrder.1 last lastMember
        have strictlyBefore : finish first < start last := by linarith
        exact (ne_of_lt strictlyBefore (contacts first (by simp) last (by simp [lastMember]) strictlyBefore.le point firstContains laterContains).1).elim
      · intro first fm last lm
        exact contacts first (List.mem_cons_of_mem _ fm) last (List.mem_cons_of_mem _ lm)

end LeanTrominoes.GridPolyline
