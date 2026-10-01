/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthSearch

/-! # Exact discovery semantics of a breadth-first adjacency scan -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

theorem visit_distance (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L)
    (w : L) (j : Nat) : (visit matching depth arcs s).distance w=some j ↔
      s.distance w=some j ∨
      (s.distance w=none ∧ j=depth+1 ∧ ∃ r ∈ arcs, matching.right r=some w) := by
  induction arcs generalizing s with
  | nil => simp [visit]
  | cons r rs ih =>
    cases mate : matching.right r with
    | none =>
      simp only [visit,mate,ih]
      simp [List.mem_cons,mate,or_and_right,exists_or]
    | some v =>
      cases known : s.distance v with
      | some i =>
        simp only [visit,mate,known,ih]
        by_cases equal : w=v
        · subst w; simp [known]
        · simp [List.mem_cons,mate,equal,Ne.symm equal,or_and_right,exists_or]
      | none =>
        simp only [visit,mate,known,ih]
        by_cases equal : w=v
        · subst w
          simp [Function.update_apply,known,List.mem_cons,mate,or_and_right,exists_or,eq_comm]
        · simp [Function.update_apply,equal,Ne.symm equal,List.mem_cons,mate,or_and_right,exists_or]

theorem visit_terminal (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L) :
    (visit matching depth arcs s).terminal=true ↔
      s.terminal=true ∨ ∃ r ∈ arcs, matching.right r=none := by
  induction arcs generalizing s with
  | nil => simp [visit]
  | cons r rs ih =>
    cases mate : matching.right r with
    | none => simp [visit,mate,ih,List.mem_cons,or_and_right,exists_or]
    | some v =>
      cases known : s.distance v <;> simp [visit,mate,known,ih,List.mem_cons,or_and_right,exists_or]

theorem visit_next (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L) (w : L) :
    w ∈ (visit matching depth arcs s).next ↔
      w ∈ s.next ∨ (s.distance w=none ∧ ∃ r ∈ arcs, matching.right r=some w) := by
  induction arcs generalizing s with
  | nil => simp [visit]
  | cons r rs ih =>
    cases mate : matching.right r with
    | none =>
      simp only [visit,mate,ih]
      simp [List.mem_cons,mate,or_and_right,exists_or]
    | some v =>
      cases known : s.distance v with
      | some i =>
        simp only [visit,mate,known,ih]
        by_cases equal : w=v
        · subst w; simp [known]
        · simp [List.mem_cons,mate,equal,Ne.symm equal,or_and_right,exists_or]
      | none =>
        simp only [visit,mate,known,ih]
        by_cases equal : w=v
        · subst w
          simp [Function.update_apply,known,List.mem_cons,mate,or_and_right,exists_or,eq_comm]
        · simp [Function.update_apply,equal,Ne.symm equal,List.mem_cons,mate,or_and_right,exists_or]

structure Tagged (depth : Nat) (s : Wave L) : Prop where
  nodup : s.next.Nodup
  label : ∀ w ∈ s.next, s.distance w=some (depth+1)

theorem visit_tagged (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L)
    (tagged : Tagged depth s) : Tagged depth (visit matching depth arcs s) := by
  induction arcs generalizing s with
  | nil => exact ⟨tagged.nodup,tagged.label⟩
  | cons r rs ih =>
    cases mate : matching.right r with
    | none => simpa only [visit,mate] using ih {s with terminal := true,cost := s.cost+5} ⟨tagged.nodup,tagged.label⟩
    | some v =>
      cases known : s.distance v with
      | some i => simpa only [visit,mate,known] using ih {s with cost := s.cost+6} ⟨tagged.nodup,tagged.label⟩
      | none =>
        simp only [visit,mate,known]
        apply ih
        have fresh : v ∉ s.next := by
          intro member
          have := tagged.label v member
          simp_all
        refine ⟨List.nodup_cons.mpr ⟨fresh,tagged.nodup⟩,?_⟩
        intro w member
        rcases List.mem_cons.mp member with equal | member
        · subst w; simp
        · have ne : w ≠ v := by intro eq; subst w; exact fresh member
          simpa [Function.update_apply,ne] using tagged.label w member

/-- Each adjacency cell is inspected once, including duplicate protoedges. -/
theorem visit_cost (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L) :
    (visit matching depth arcs s).cost ≤ s.cost+10*arcs.length+1 := by
  induction arcs generalizing s with
  | nil => simp [visit]
  | cons r rs ih =>
    cases mate : matching.right r with
    | none => have later := ih {s with terminal := true,cost := s.cost+5}; simp only [visit,mate,List.length_cons] at *; omega
    | some v =>
      cases known : s.distance v with
      | some i => have later := ih {s with cost := s.cost+6}; simp only [visit,mate,known,List.length_cons] at *; omega
      | none =>
        have later := ih {s with distance := Function.update s.distance v (some (depth+1)),
                                 next := v::s.next,cost := s.cost+10}
        simp only [visit,mate,known,List.length_cons] at *
        omega

end LeanTrominoes.BipartiteMatching.BreadthSearch
