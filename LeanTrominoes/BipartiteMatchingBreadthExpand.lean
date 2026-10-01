/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthVisit

/-! # Exact semantics and charge of one complete breadth-first wave -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

theorem visit_none (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L) (w : L) :
    (visit matching depth arcs s).distance w=none ↔
      s.distance w=none ∧ ¬ ∃ r ∈ arcs, matching.right r=some w := by
  constructor
  · intro absent
    have old : s.distance w=none := by
      cases known : s.distance w with
      | none => rfl
      | some j =>
        have marked := (visit_distance matching depth arcs s w j).mpr (Or.inl known)
        simp_all
    refine ⟨old,?_⟩
    intro member
    have marked := (visit_distance matching depth arcs s w (depth+1)).mpr (Or.inr ⟨old,rfl,member⟩)
    simp_all
  · rintro ⟨old,absent⟩
    cases known : (visit matching depth arcs s).distance w with
    | none => rfl
    | some j =>
      rcases (visit_distance matching depth arcs s w j).mp known with previous | ⟨_,_,member⟩
      · simp_all
      · exact (absent member).elim

theorem expand_distance (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) (w : L) (j : Nat) :
    (expand buckets matching depth frontier s).distance w=some j ↔
      s.distance w=some j ∨ (s.distance w=none ∧ j=depth+1 ∧
        ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=some w) := by
  classical
  induction frontier generalizing s with
  | nil => simp [expand]
  | cons v vs ih =>
    simp only [expand,ih,visit_distance,visit_none]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
    by_cases discovered : ∃ r ∈ buckets v, matching.right r=some w
    · simp [discovered,and_assoc]
    · simp [discovered,and_assoc]

theorem expand_terminal (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) :
    (expand buckets matching depth frontier s).terminal=true ↔
      s.terminal=true ∨ ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=none := by
  classical
  induction frontier generalizing s with
  | nil => simp [expand]
  | cons v vs ih =>
    simp only [expand,ih,visit_terminal]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
    exact or_assoc

theorem expand_next (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) (w : L) :
    w ∈ (expand buckets matching depth frontier s).next ↔
      w ∈ s.next ∨ (s.distance w=none ∧
        ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=some w) := by
  classical
  induction frontier generalizing s with
  | nil => simp [expand]
  | cons v vs ih =>
    simp only [expand,ih,visit_next,visit_none]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
    by_cases discovered : ∃ r ∈ buckets v, matching.right r=some w
    · simp [discovered,and_assoc]
    · simp [discovered,and_assoc]

theorem expand_tagged (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) (tagged : Tagged depth s) :
    Tagged depth (expand buckets matching depth frontier s) := by
  classical
  induction frontier generalizing s with
  | nil => exact ⟨tagged.nodup,tagged.label⟩
  | cons v vs ih =>
    exact ih _ (visit_tagged matching depth (buckets v) {s with cost := s.cost+3}
      ⟨tagged.nodup,tagged.label⟩)

theorem expand_cost (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) :
    (expand buckets matching depth frontier s).cost ≤
      s.cost+4*frontier.length+10*(frontier.map (fun v => (buckets v).length)).sum+1 := by
  classical
  induction frontier generalizing s with
  | nil => simp [expand]
  | cons v vs ih =>
    have first := visit_cost matching depth (buckets v) {s with cost := s.cost+3}
    have later := ih (visit matching depth (buckets v) {s with cost := s.cost+3})
    simp only [expand,List.length_cons,List.map_cons,List.sum_cons] at *
    omega

end LeanTrominoes.BipartiteMatching.BreadthSearch
