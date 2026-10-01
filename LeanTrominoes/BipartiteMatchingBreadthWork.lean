/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthStep

/-! # Amortizing breadth-first waves over disjoint adjacency lists -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def past (distance : L → Option Nat) (depth : Nat) (l : L) : Prop :=
  (distance l).isSome=true ∧ (distance l).getD depth < depth

instance (distance : L → Option Nat) (depth : Nat) (l : L) : Decidable (past distance depth l) :=
  inferInstanceAs (Decidable ((distance l).isSome=true ∧ (distance l).getD depth < depth))

def work (buckets : L → List R) (distance : L → Option Nat) (depth : Nat) : Nat :=
  ∑ l, if past distance depth l then 0 else (buckets l).length+1

theorem sum_list_set (f : L → Nat) (ls : List L) (nodup : ls.Nodup) :
    (∑ l ∈ ls.toFinset, f l)=(ls.map f).sum := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have absent : l ∉ ls.toFinset := by simpa using (List.nodup_cons.mp nodup).1
    simp only [List.toFinset_cons,List.map_cons,List.sum_cons]
    rw [Finset.sum_insert absent,ih (List.nodup_cons.mp nodup).2]

theorem weighted_frontier (buckets : L → List R) (frontier : List L) :
    (frontier.map (fun l => (buckets l).length+1)).sum=
      (frontier.map (fun l => (buckets l).length)).sum+frontier.length := by
  induction frontier with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons,List.sum_cons,List.length_cons]; omega

theorem frontier_set (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) : frontier.toFinset=layer distance depth := by
  ext l
  simp only [List.mem_toFinset,layer,Finset.mem_filter,Finset.mem_univ,true_and]
  exact inv.frontier_mem l

theorem frontier_length (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) : freeCount ≤ frontier.length := by
  have growth := inv.growth depth (le_refl _)
  rw [← frontier_set buckets matching freeCount depth frontier distance inv,
    List.toFinset_card_of_nodup inv.frontier_nodup] at growth
  exact growth

theorem work_balance (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    work buckets (wave buckets matching depth frontier distance).distance (depth+1)+
      (frontier.map (fun l => (buckets l).length)).sum+frontier.length=work buckets distance depth := by
  have point (l : L) : (if past distance depth l then 0 else (buckets l).length+1)=
      (if past (wave buckets matching depth frontier distance).distance (depth+1) l then 0 else (buckets l).length+1)+
      (if distance l=some depth then (buckets l).length+1 else 0) := by
    cases old : distance l with
    | some j =>
      have new := wave_old buckets matching depth frontier distance l j old
      have bounded := inv.bounded l j old
      by_cases equal : j=depth
      · subst j; simp [past,old,new]
      · have before : j < depth := by omega
        simp [past,old,new,before,show j < depth+1 by omega,show j ≠ depth from equal]
    | none =>
      cases new : (wave buckets matching depth frontier distance).distance l with
      | none => simp [past,old,new]
      | some j =>
        rcases (wave_distance ..).mp new with marked | ⟨_,equal,_⟩
        · simp_all
        · simp [past,old,new,equal]
  have sum : work buckets distance depth=
      work buckets (wave buckets matching depth frontier distance).distance (depth+1)+
        ∑ l, if distance l=some depth then (buckets l).length+1 else 0 := by
    unfold work
    simp_rw [point]
    rw [Finset.sum_add_distrib]
  have front := frontier_set buckets matching freeCount depth frontier distance inv
  have weighted := sum_list_set (fun l => (buckets l).length+1) frontier inv.frontier_nodup
  have filtered : (∑ l, if distance l=some depth then (buckets l).length+1 else 0)=
      ∑ l ∈ layer distance depth, ((buckets l).length+1) := by
    simp [layer,Finset.sum_filter]
  rw [filtered,← front,weighted,weighted_frontier] at sum
  omega

theorem visit_next_length (matching : State L R) (depth : Nat) (arcs : List R) (s : Wave L) :
    (visit matching depth arcs s).next.length ≤ s.next.length+arcs.length := by
  induction arcs generalizing s with
  | nil => simp [visit]
  | cons r rs ih =>
    cases mate : matching.right r with
    | none =>
      have later := ih {s with terminal := true,cost := s.cost+5}
      simp only [visit,mate,List.length_cons] at *
      omega
    | some v =>
      cases known : s.distance v with
      | some j =>
        have later := ih {s with cost := s.cost+6}
        simp only [visit,mate,known,List.length_cons] at *
        omega
      | none =>
        have later := ih {s with distance := Function.update s.distance v (some (depth+1)),
                                 next := v::s.next,cost := s.cost+10}
        simp only [visit,mate,known,List.length_cons] at *
        omega

theorem expand_next_length (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (s : Wave L) :
    (expand buckets matching depth frontier s).next.length ≤
      s.next.length+(frontier.map (fun l => (buckets l).length)).sum := by
  induction frontier generalizing s with
  | nil => simp [expand]
  | cons v vs ih =>
    have first := visit_next_length matching depth (buckets v) {s with cost := s.cost+3}
    have later := ih (visit matching depth (buckets v) {s with cost := s.cost+3})
    simp only [expand,List.map_cons,List.sum_cons] at *
    omega

end LeanTrominoes.BipartiteMatching.BreadthSearch
