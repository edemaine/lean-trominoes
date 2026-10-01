/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthExpand

/-! # Layer, predecessor, and Hall-growth invariants -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def layer (distance : L → Option Nat) (j : Nat) : Finset L :=
  Finset.univ.filter (fun l => distance l=some j)

def reached (distance : L → Option Nat) : Finset L := Finset.univ.filter (fun l => distance l ≠ none)
def freeSet (matching : State L R) : Finset L := Finset.univ.filter (fun l => matching.left l=none)

structure Invariant (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat) : Prop where
  count : freeCount=(freeSet matching).card
  zero : ∀ l, distance l=some 0 ↔ matching.left l=none
  bounded : ∀ l j, distance l=some j → j ≤ depth
  parent : ∀ l j, distance l=some (j+1) →
    ∃ v, distance v=some j ∧ ∃ r ∈ buckets v, matching.right r=some l
  processed : ∀ l j, distance l=some j → j < depth → ∀ r ∈ buckets l,
    ∃ w, matching.right r=some w ∧ ∃ i ≤ j+1, distance w=some i
  frontier_nodup : frontier.Nodup
  frontier_mem : ∀ l, l ∈ frontier ↔ distance l=some depth
  growth : ∀ j ≤ depth, freeCount ≤ (layer distance j).card

theorem layers_density (distance : L → Option Nat) (freeCount depth : Nat)
    (growth : ∀ j ≤ depth, freeCount ≤ (layer distance j).card) :
    freeCount*(depth+1) ≤ Fintype.card L := by
  have disjoint : (Finset.range (depth+1) : Set Nat).PairwiseDisjoint (layer distance) := by
    intro i hi j hj different
    apply Finset.disjoint_left.mpr
    intro l one two
    simp only [layer,Finset.mem_filter,Finset.mem_univ,true_and] at one two
    have same : i=j := Option.some.inj (one.symm.trans two)
    exact different same
  have sum := Finset.sum_le_sum (s := Finset.range (depth+1))
    (f := fun _ => freeCount) (g := fun j => (layer distance j).card)
    (fun j hj => growth j (by have := Finset.mem_range.mp hj; omega))
  have card := Finset.card_biUnion disjoint
  have bound := Finset.card_le_univ ((Finset.range (depth+1)).biUnion (layer distance))
  rw [card] at bound
  have equal : (∑ _j ∈ Finset.range (depth+1), freeCount)=freeCount*(depth+1) := by simp [Nat.mul_comm]
  rw [equal] at sum
  exact sum.trans bound

theorem initial_invariant (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R) :
    Invariant buckets matching (freeVertices vertices matching).length 0
      (freeVertices vertices matching) (initialDistance matching) := by
  have univ : vertices.toFinset=Finset.univ := by ext l; simp [complete]
  have filtered : (freeVertices vertices matching).toFinset=freeSet matching := by
    simp [freeVertices,freeSet,List.toFinset_filter,univ]
  have freeNodup : (freeVertices vertices matching).Nodup := nodup.filter _
  have count : (freeVertices vertices matching).length=(freeSet matching).card := by
    rw [← List.toFinset_card_of_nodup freeNodup,filtered]
  refine ⟨count,?_,?_,?_,?_,freeNodup,?_,?_⟩
  · intro l; simp [initialDistance]
  · intro l j marked
    unfold initialDistance at marked
    split at marked
    · have := Option.some.inj marked; omega
    · simp at marked
  · intro l j marked
    unfold initialDistance at marked
    split at marked <;> simp_all
  · intro l j marked before r member; omega
  · intro l
    simp [freeVertices,initialDistance,complete]
  · intro j hj
    have equal : j=0 := by omega
    subst j
    have same : layer (initialDistance matching) 0=freeSet matching := by
      ext l; simp [layer,initialDistance,freeSet]
    rw [same,← count]

end LeanTrominoes.BipartiteMatching.BreadthSearch
