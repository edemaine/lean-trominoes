/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthCard

/-! # A failed growth test provides an explicit Hall deficiency -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def prefixSet (distance : L → Option Nat) (depth : Nat) : Finset L :=
  Finset.univ.filter (fun l => (distance l).isSome=true ∧ (distance l).getD (depth+1) ≤ depth)

theorem wave_prefix (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    prefixSet (wave buckets matching depth frontier distance).distance depth=reached distance := by
  ext l
  cases old : distance l with
  | some j =>
    have new := wave_old buckets matching depth frontier distance l j old
    have bound := inv.bounded l j old
    simp [prefixSet,reached,old,new,bound]
  | none =>
    cases new : (wave buckets matching depth frontier distance).distance l with
    | none => simp [prefixSet,reached,old,new]
    | some j =>
      rcases (wave_distance ..).mp new with marked | ⟨_,equal,_⟩
      · simp_all
      · simp [prefixSet,reached,old,new,equal]

theorem source_neighbor (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (noTerminal : (wave buckets matching depth frontier distance).terminal=false)
    (l : L) (marked : l ∈ reached distance) (r : R) (edge : r ∈ buckets l) :
    ∃ w, matching.right r=some w ∧ w ∈ reached (wave buckets matching depth frontier distance).distance := by
  have notNone : distance l ≠ none := (Finset.mem_filter.mp marked).2
  cases label : distance l with
  | none => exact (notNone label).elim
  | some j =>
    by_cases before : j < depth
    · obtain ⟨w,mate,i,hi,known⟩ := inv.processed l j label before r edge
      have new := wave_old buckets matching depth frontier distance w i known
      exact ⟨w,mate,by simp [reached,new]⟩
    · have equal : j=depth := by have bound := inv.bounded l j label; omega
      subst j
      have member := (inv.frontier_mem l).mpr label
      cases mate : matching.right r with
      | none =>
        have hit := (wave_terminal buckets matching depth frontier distance).mpr ⟨l,member,r,edge,mate⟩
        simp_all
      | some w =>
        obtain ⟨i,hi,known⟩ := wave_neighbor buckets matching freeCount depth frontier distance inv l member r edge w mate
        exact ⟨w,rfl,by simp [reached,known]⟩

theorem wave_hall (buckets : L → List R) (matching : State L R) (consistent : Consistent matching)
    (freeCount depth : Nat) (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (noTerminal : (wave buckets matching depth frontier distance).terminal=false)
    (deficient : (wave buckets matching depth frontier distance).next.length < freeCount) :
    (neighborSet buckets (prefixSet (wave buckets matching depth frontier distance).distance depth)).card <
      (prefixSet (wave buckets matching depth frontier distance).distance depth).card := by
  rw [wave_prefix buckets matching freeCount depth frontier distance inv]
  have freeSubset : freeSet matching ⊆ reached (wave buckets matching depth frontier distance).distance := by
    rw [wave_reached]
    intro l member
    apply Finset.mem_union.mpr
    exact Or.inl (free_subset buckets matching freeCount depth frontier distance inv member)
  have count := matching_card matching consistent
    (reached (wave buckets matching depth frontier distance).distance \ freeSet matching)
    (neighborSet buckets (reached distance)) (by
      intro l member
      obtain ⟨marked,notFree⟩ := Finset.mem_sdiff.mp member
      have known : (wave buckets matching depth frontier distance).distance l ≠ none := (Finset.mem_filter.mp marked).2
      cases label : (wave buckets matching depth frontier distance).distance l with
      | none => exact (known label).elim
      | some j =>
        cases j with
        | zero =>
          have old := (wave_low buckets matching freeCount depth frontier distance inv l 0 (Nat.zero_le _)).mp label
          have free := (inv.zero l).mp old
          exact (notFree (by simp [freeSet,free])).elim
        | succ j =>
          obtain ⟨v,old,r,edge,mate⟩ := wave_parent buckets matching freeCount depth frontier distance inv l j label
          refine ⟨r,(mem_neighborSet buckets _ r).mpr ⟨v,by simp [reached,old],edge⟩,(consistent l r).mpr mate⟩)
    (by
      intro r member
      obtain ⟨l,marked,edge⟩ := (mem_neighborSet buckets _ r).mp member
      obtain ⟨w,mate,new⟩ := source_neighbor buckets matching freeCount depth frontier distance inv noTerminal l marked r edge
      have paired := (consistent w r).mpr mate
      exact ⟨w,Finset.mem_sdiff.mpr ⟨new,by simp [freeSet,paired]⟩,mate⟩)
  rw [Finset.card_sdiff_of_subset freeSubset,wave_reached_card,← inv.count] at count
  have oldCount : freeCount ≤ (reached distance).card := by
    rw [inv.count]
    exact Finset.card_le_card (free_subset buckets matching freeCount depth frontier distance inv)
  omega

end LeanTrominoes.BipartiteMatching.BreadthSearch
