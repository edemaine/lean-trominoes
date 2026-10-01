/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthWave
import LeanTrominoes.BipartiteMatchingCardinality

/-! # The cardinality accounting of one breadth-first wave -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

theorem wave_reached (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    reached (wave buckets matching depth frontier distance).distance=
      reached distance ∪ (wave buckets matching depth frontier distance).next.toFinset := by
  ext l
  simp only [reached,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,List.mem_toFinset]
  constructor
  · intro marked
    cases label : (wave buckets matching depth frontier distance).distance l with
    | none => exact (marked label).elim
    | some j =>
      rcases (wave_distance ..).mp label with old | ⟨fresh,_,member⟩
      · exact Or.inl (by simp [old])
      · exact Or.inr ((wave_next ..).mpr ⟨fresh,member⟩)
  · rintro (old | member)
    · cases label : distance l with
      | none => exact (old label).elim
      | some j => have new := wave_old buckets matching depth frontier distance l j label; simp [new]
    · have new := (wave_tagged buckets matching depth frontier distance).label l member
      simp [new]

theorem wave_disjoint (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    Disjoint (reached distance) (wave buckets matching depth frontier distance).next.toFinset := by
  apply Finset.disjoint_left.mpr
  intro l old member
  have fresh := ((wave_next ..).mp (List.mem_toFinset.mp member)).1
  simp [reached,fresh] at old

theorem wave_reached_card (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    (reached (wave buckets matching depth frontier distance).distance).card=
      (reached distance).card+(wave buckets matching depth frontier distance).next.length := by
  rw [wave_reached,Finset.card_union_of_disjoint (wave_disjoint ..),
    List.toFinset_card_of_nodup (wave_tagged buckets matching depth frontier distance).nodup]

theorem wave_parent (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) (l : L) (j : Nat)
    (marked : (wave buckets matching depth frontier distance).distance l=some (j+1)) :
    ∃ v, distance v=some j ∧ ∃ r ∈ buckets v, matching.right r=some l := by
  rcases (wave_distance ..).mp marked with old | ⟨_,equal,v,member,r,edge,mate⟩
  · exact inv.parent l j old
  · have equal : j=depth := by omega
    subst j
    exact ⟨v,(inv.frontier_mem v).mp member,r,edge,mate⟩

theorem free_subset (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) : freeSet matching ⊆ reached distance := by
  intro l member
  have free : matching.left l=none := (Finset.mem_filter.mp member).2
  have zero := (inv.zero l).mpr free
  simp [reached,zero]

end LeanTrominoes.BipartiteMatching.BreadthSearch
