/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthInvariant

/-! # Discovery and preservation facts for a fresh breadth-first wave -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def wave (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) : Wave L :=
  expand buckets matching depth frontier ⟨distance,[],false,0⟩

theorem wave_distance (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) (l : L) (j : Nat) :
    (wave buckets matching depth frontier distance).distance l=some j ↔
      distance l=some j ∨ (distance l=none ∧ j=depth+1 ∧
        ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=some l) := by
  exact expand_distance buckets matching depth frontier ⟨distance,[],false,0⟩ l j

theorem wave_next (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) (l : L) :
    l ∈ (wave buckets matching depth frontier distance).next ↔
      distance l=none ∧ ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=some l := by
  simpa [wave] using expand_next buckets matching depth frontier ⟨distance,[],false,0⟩ l

theorem wave_terminal (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    (wave buckets matching depth frontier distance).terminal=true ↔
      ∃ v ∈ frontier, ∃ r ∈ buckets v, matching.right r=none := by
  simpa [wave] using expand_terminal buckets matching depth frontier ⟨distance,[],false,0⟩

theorem wave_tagged (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) :
    Tagged depth (wave buckets matching depth frontier distance) :=
  expand_tagged buckets matching depth frontier _ ⟨by simp,by simp⟩

theorem wave_old (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) (l : L) (j : Nat) (known : distance l=some j) :
    (wave buckets matching depth frontier distance).distance l=some j :=
  (wave_distance ..).mpr (Or.inl known)

theorem wave_bounded (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) (l : L) (j : Nat)
    (marked : (wave buckets matching depth frontier distance).distance l=some j) : j ≤ depth+1 := by
  rcases (wave_distance ..).mp marked with old | ⟨_,equal,_⟩
  · exact (inv.bounded l j old).trans (Nat.le_succ _)
  · omega

theorem wave_low (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) (l : L) (j : Nat)
    (low : j ≤ depth) : (wave buckets matching depth frontier distance).distance l=some j ↔ distance l=some j := by
  rw [wave_distance]
  constructor
  · rintro (old | ⟨_,equal,_⟩)
    · exact old
    · omega
  · exact Or.inl

theorem wave_layer_low (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) (j : Nat) (low : j ≤ depth) :
    layer (wave buckets matching depth frontier distance).distance j=layer distance j := by
  ext l
  simp only [layer,Finset.mem_filter,Finset.mem_univ,true_and]
  exact wave_low buckets matching freeCount depth frontier distance inv l j low

theorem wave_frontier_mem (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) (l : L) :
    l ∈ (wave buckets matching depth frontier distance).next ↔
      (wave buckets matching depth frontier distance).distance l=some (depth+1) := by
  constructor
  · exact (wave_tagged buckets matching depth frontier distance).label l
  · intro marked
    rcases (wave_distance ..).mp marked with old | ⟨fresh,_,member⟩
    · have bound := inv.bounded l (depth+1) old; omega
    · exact (wave_next ..).mpr ⟨fresh,member⟩

theorem wave_neighbor (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (v : L) (member : v ∈ frontier) (r : R) (edge : r ∈ buckets v) (w : L)
    (mate : matching.right r=some w) :
    ∃ j ≤ depth+1, (wave buckets matching depth frontier distance).distance w=some j := by
  cases known : distance w with
  | some j => exact ⟨j,(inv.bounded w j known).trans (Nat.le_succ _),wave_old _ _ _ _ _ w j known⟩
  | none => exact ⟨depth+1,le_refl _,(wave_distance ..).mpr (Or.inr ⟨known,rfl,v,member,r,edge,mate⟩)⟩

end LeanTrominoes.BipartiteMatching.BreadthSearch
