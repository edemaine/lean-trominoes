/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingBreadthWave
import LeanTrominoes.BipartiteMatchingLayers

/-! # Successful breadth-first searches certify a shortest level graph -/
namespace LeanTrominoes.BipartiteMatching.BreadthSearch
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

def height (distance : L → Option Nat) (depth : Nat) (l : L) : Nat :=
  min ((distance l).getD depth) depth

theorem height_bound (distance : L → Option Nat) (depth : Nat) (l : L) : height distance depth l ≤ depth :=
  Nat.min_le_right _ _

theorem wave_height_old (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (l : L) (j : Nat) (marked : distance l=some j) :
    height (wave buckets matching depth frontier distance).distance (depth+1) l=j := by
  have new := wave_old buckets matching depth frontier distance l j marked
  have bound := inv.bounded l j marked
  simp [height,new,Nat.min_eq_left (by omega : j ≤ depth+1)]

theorem wave_height_unknown (buckets : L → List R) (matching : State L R) (depth : Nat)
    (frontier : List L) (distance : L → Option Nat) (l : L) (unknown : distance l=none) :
    height (wave buckets matching depth frontier distance).distance (depth+1) l=depth+1 := by
  cases marked : (wave buckets matching depth frontier distance).distance l with
  | none => simp [height,marked]
  | some j =>
    rcases (wave_distance ..).mp marked with old | ⟨_,equal,_⟩
    · simp_all
    · simp [height,marked,equal]

theorem wave_labels (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance) :
    Labels buckets matching (height (wave buckets matching depth frontier distance).distance (depth+1)) (depth+1) := by
  refine ⟨?_,?_⟩
  · intro l free
    exact wave_height_old buckets matching freeCount depth frontier distance inv l 0 ((inv.zero l).mpr free)
  · intro l r edge
    cases old : distance l with
    | none =>
      rw [wave_height_unknown buckets matching depth frontier distance l old]
      cases mate : matching.right r with
      | none => omega
      | some w => have bound := height_bound (wave buckets matching depth frontier distance).distance (depth+1) w; omega
    | some j =>
      rw [wave_height_old buckets matching freeCount depth frontier distance inv l j old]
      by_cases before : j < depth
      · obtain ⟨w,mate,i,hi,known⟩ := inv.processed l j old before r edge
        simp only [mate]
        rw [wave_height_old buckets matching freeCount depth frontier distance inv w i known]
        exact hi
      · have equal : j=depth := by have bound := inv.bounded l j old; omega
        subst j
        cases mate : matching.right r with
        | none => omega
        | some w =>
          obtain ⟨i,hi,known⟩ := wave_neighbor buckets matching freeCount depth frontier distance inv l
            ((inv.frontier_mem l).mpr old) r edge w mate
          simp [height,known,Nat.min_eq_left hi,hi]

/-- Predecessor links prepend a level route until a free root is reached. -/
theorem prepend_predecessors (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (labels : L → Nat) (terminalDepth : Nat)
    (exactHeight : ∀ l j, distance l=some j → labels l=j)
    (j : Nat) (l : L) (marked : distance l=some j) (p : Route L R) (first : p.first=l)
    (follows : Follows (levelBuckets buckets matching labels terminalDepth) p) :
    ∃ q : Route L R, Follows (levelBuckets buckets matching labels terminalDepth) q ∧ matching.left q.first=none := by
  induction j generalizing l p with
  | zero => exact ⟨p,follows,first ▸ (inv.zero l).mp marked⟩
  | succ j ih =>
    obtain ⟨v,previous,r,edge,mate⟩ := inv.parent l j marked
    have arc : (r,some p.first) ∈ levelBuckets buckets matching labels terminalDepth v := by
      apply (mem_levelBuckets ..).mpr
      refine ⟨edge,by simpa [first] using mate,?_⟩
      rw [first,exactHeight l (j+1) marked,exactHeight v j previous]
    exact ih v previous (.cons v r p) rfl (Follows.cons arc follows)

theorem wave_short_route (buckets : L → List R) (matching : State L R) (freeCount depth : Nat)
    (frontier : List L) (distance : L → Option Nat)
    (inv : Invariant buckets matching freeCount depth frontier distance)
    (terminal : (wave buckets matching depth frontier distance).terminal=true) :
    ∃ p : Route L R,
      Follows (levelBuckets buckets matching
        (height (wave buckets matching depth frontier distance).distance (depth+1)) (depth+1)) p ∧
      matching.left p.first=none := by
  obtain ⟨v,member,r,edge,free⟩ := (wave_terminal ..).mp terminal
  have known := (inv.frontier_mem v).mp member
  have leaf : Follows (levelBuckets buckets matching
      (height (wave buckets matching depth frontier distance).distance (depth+1)) (depth+1)) (.last v r) := by
    apply Follows.last
    apply (mem_levelBuckets ..).mpr
    refine ⟨edge,free,?_⟩
    rw [wave_height_old buckets matching freeCount depth frontier distance inv v depth known]
  exact prepend_predecessors buckets matching freeCount depth frontier distance inv _ _
    (wave_height_old buckets matching freeCount depth frontier distance inv) depth v known (.last v r) rfl leaf

end LeanTrominoes.BipartiteMatching.BreadthSearch
