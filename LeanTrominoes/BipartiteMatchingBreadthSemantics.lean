/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthLabels
import LeanTrominoes.BipartiteMatchingBreadthHall
import LeanTrominoes.BipartiteMatchingBreadthStep

/-! # A complete shortest-layer or Hall-deficiency certificate -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def Spec (buckets : L → List R) (matching : State L R) (freeCount : Nat) : Outcome L → Prop
  | .layers distance depth _ =>
    Labels buckets matching (height distance depth) depth ∧
    freeCount*depth ≤ Fintype.card L ∧ 0 < depth ∧
    ∃ p : Route L R, Follows (levelBuckets buckets matching (height distance depth) depth) p ∧ matching.left p.first=none
  | .deficient distance depth _ =>
    (neighborSet buckets (prefixSet distance depth)).card < (prefixSet distance depth).card
  | .exhausted _ => False

theorem run_spec (buckets : L → List R) (matching : State L R) (consistent : Consistent matching)
    (freeCount : Nat) (positive : 0 < freeCount) (fuel depth : Nat) (frontier : List L)
    (distance : L → Option Nat) (enough : depth+fuel=Fintype.card L)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    Spec buckets matching freeCount (run buckets matching freeCount fuel depth frontier distance) := by
  induction fuel generalizing depth frontier distance with
  | zero =>
    have density := layers_density distance freeCount depth inv.growth
    have bound : depth+1 ≤ freeCount*(depth+1) := Nat.le_mul_of_pos_left _ positive
    simp only [Nat.add_zero] at enough
    omega
  | succ fuel ih =>
    change Spec buckets matching freeCount
      (if (wave buckets matching depth frontier distance).terminal then
        .layers (wave buckets matching depth frontier distance).distance (depth+1)
          ((wave buckets matching depth frontier distance).cost+3)
       else if (wave buckets matching depth frontier distance).next.length < freeCount then
        .deficient (wave buckets matching depth frontier distance).distance depth
          ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+4)
       else match run buckets matching freeCount fuel (depth+1)
          (wave buckets matching depth frontier distance).next (wave buckets matching depth frontier distance).distance with
        | .layers labels height cost => .layers labels height
            ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+5+cost)
        | .deficient labels height cost => .deficient labels height
            ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+5+cost)
        | .exhausted cost => .exhausted
            ((wave buckets matching depth frontier distance).cost+(wave buckets matching depth frontier distance).next.length+5+cost))
    cases terminal : (wave buckets matching depth frontier distance).terminal with
    | true =>
      simp only [terminal,if_true,Spec]
      exact ⟨wave_labels buckets matching freeCount depth frontier distance inv,
        layers_density distance freeCount depth inv.growth,by omega,
        wave_short_route buckets matching freeCount depth frontier distance inv terminal⟩
    | false =>
      simp only [terminal,Bool.false_eq_true,if_false]
      by_cases deficient : (wave buckets matching depth frontier distance).next.length < freeCount
      · simp only [deficient,if_true,Spec]
        exact wave_hall buckets matching consistent freeCount depth frontier distance inv terminal deficient
      · simp only [deficient,if_false]
        have nextInv := wave_invariant buckets matching freeCount depth frontier distance inv terminal (by omega)
        have later := ih (depth+1) (wave buckets matching depth frontier distance).next
          (wave buckets matching depth frontier distance).distance (by omega) nextInv
        cases found : run buckets matching freeCount fuel (depth+1)
            (wave buckets matching depth frontier distance).next (wave buckets matching depth frontier distance).distance <;>
          simpa only [found,Spec] using later

theorem vertices_length (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices) :
    vertices.length=Fintype.card L := by
  have equal : vertices.toFinset=Finset.univ := by ext l; simp [complete]
  rw [← List.toFinset_card_of_nodup nodup,equal,Finset.card_univ]

theorem search_spec (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R) (consistent : Consistent matching)
    (positive : 0 < (freeVertices vertices matching).length) :
    Spec buckets matching (freeVertices vertices matching).length (search vertices buckets matching) := by
  apply run_spec buckets matching consistent _ positive
  · simp [vertices_length vertices nodup complete]
  · exact initial_invariant vertices nodup complete buckets matching

end LeanTrominoes.BipartiteMatching.BreadthSearch
