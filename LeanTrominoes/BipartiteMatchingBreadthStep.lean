/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthWave

/-! # Preserving the breadth-first invariant after a nonterminal wave -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

theorem wave_invariant (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (noTerminal : (wave buckets matching depth frontier distance).terminal=false)
    (growth : freeCount ≤ (wave buckets matching depth frontier distance).next.length) :
    Invariant buckets matching freeCount (depth+1)
      (wave buckets matching depth frontier distance).next
      (wave buckets matching depth frontier distance).distance := by
  have tagged := wave_tagged buckets matching depth frontier distance
  refine ⟨inv.count,?_,wave_bounded buckets matching freeCount depth frontier distance inv,
    ?_,?_,tagged.nodup,wave_frontier_mem buckets matching freeCount depth frontier distance inv,?_⟩
  · intro l
    exact (wave_low buckets matching freeCount depth frontier distance inv l 0 (Nat.zero_le _)).trans (inv.zero l)
  · intro l j marked
    rcases (wave_distance ..).mp marked with old | ⟨_,equal,v,hv,r,hr,mate⟩
    · obtain ⟨v,previous,r,edge,mate⟩ := inv.parent l j old
      exact ⟨v,wave_old _ _ _ _ _ v j previous,r,edge,mate⟩
    · have depthEq : j=depth := by omega
      subst j
      have previous := (inv.frontier_mem v).mp hv
      exact ⟨v,wave_old _ _ _ _ _ v depth previous,r,hr,mate⟩
  · intro l j marked before r edge
    have low : j ≤ depth := by omega
    have old := (wave_low buckets matching freeCount depth frontier distance inv l j low).mp marked
    by_cases earlier : j < depth
    · obtain ⟨w,mate,i,hi,known⟩ := inv.processed l j old earlier r edge
      exact ⟨w,mate,i,hi,wave_old _ _ _ _ _ w i known⟩
    · have equal : j=depth := by omega
      subst j
      have member := (inv.frontier_mem l).mpr old
      cases mate : matching.right r with
      | none =>
        have terminal := (wave_terminal buckets matching depth frontier distance).mpr ⟨l,member,r,edge,mate⟩
        simp_all
      | some w =>
        obtain ⟨i,hi,known⟩ := wave_neighbor buckets matching freeCount depth frontier distance inv l member r edge w mate
        exact ⟨w,rfl,i,hi,known⟩
  · intro j hj
    by_cases low : j ≤ depth
    · rw [wave_layer_low buckets matching freeCount depth frontier distance inv j low]
      exact inv.growth j low
    · have equal : j=depth+1 := by omega
      subst j
      have setEq : (wave buckets matching depth frontier distance).next.toFinset=
          layer (wave buckets matching depth frontier distance).distance (depth+1) := by
        ext l
        simp only [List.mem_toFinset,layer,Finset.mem_filter,Finset.mem_univ,true_and]
        exact wave_frontier_mem buckets matching freeCount depth frontier distance inv l
      rw [← setEq,List.toFinset_card_of_nodup tagged.nodup]
      exact growth

end LeanTrominoes.BipartiteMatching.BreadthSearch
