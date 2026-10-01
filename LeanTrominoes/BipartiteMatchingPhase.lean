/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingSolver

/-! # Complete phase correctness and cost -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def NoShort (buckets : L → List R) (matching : State L R) (depth : Nat) : Prop :=
  ¬ ∃ p : Route L R, Alternating (fun l r => r ∈ buckets l) matching p ∧
    matching.left p.first=none ∧ p.vertices.length ≤ depth

theorem noShort_zero (buckets : L → List R) (matching : State L R) : NoShort buckets matching 0 := by
  rintro ⟨p,_,_,short⟩
  cases p <;> simp [Route.vertices] at short

theorem phase_correct (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R) (consistent : Consistent matching)
    (supported : Supported (fun l r => r ∈ buckets l) matching)
    (distance : L → Option Nat) (depth : Nat)
    (labels : Labels buckets matching (BreadthSearch.height distance depth) depth)
    (route : ∃ p : Route L R,
      Follows (levelBuckets buckets matching (BreadthSearch.height distance depth) depth) p ∧ matching.left p.first=none) :
    Consistent (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1 ∧
    Supported (fun l r => r ∈ buckets l) (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1 ∧
    (BreadthSearch.freeVertices vertices (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1).length+1 ≤
      (BreadthSearch.freeVertices vertices matching).length ∧
    NoShort buckets (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1 depth := by
  let roots := BreadthSearch.freeVertices vertices matching
  have free : ∀ l ∈ roots, matching.left l=none := fun l hl => (free_mem vertices matching l).mp hl |>.2
  have all : ∀ l, matching.left l=none → l ∈ roots := fun l hl => (free_mem vertices matching l).mpr ⟨complete l,hl⟩
  have family := blocking_family buckets matching (BreadthSearch.height distance depth) depth roots free
  obtain ⟨good,edges,growth⟩ := family.correct consistent supported
  have nonempty := blocking_nonempty (levelBuckets buckets matching (BreadthSearch.height distance depth) depth) roots
    (by obtain ⟨p,hp,hfree⟩ := route; exact ⟨p,hp,all p.first hfree⟩)
  have positive : 0 < (batch (levelBuckets buckets matching (BreadthSearch.height distance depth) depth)
      (Fintype.card L) roots initial).paths.length := by
    apply Nat.pos_of_ne_zero
    intro h
    exact nonempty (List.length_eq_zero_iff.mp h)
  rw [phase_state]
  refine ⟨good,edges,?_,blocking_no_short buckets matching consistent supported _ depth labels roots free all⟩
  rw [freeVertices_card vertices nodup complete,freeVertices_card vertices nodup complete]
  have old := free_size matching
  have final := free_size (applyRoutes matching (batch (levelBuckets buckets matching (BreadthSearch.height distance depth) depth)
    (Fintype.card L) roots initial).paths)
  dsimp only [roots] at *
  omega

theorem phase_cost (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R) (distance : L → Option Nat) (depth : Nat) :
    (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).2 ≤
      30*(∑ l, (buckets l).length)+54*Fintype.card L+4*Fintype.card R+7 := by
  let roots := BreadthSearch.freeVertices vertices matching
  let levels := levelBuckets buckets matching (BreadthSearch.height distance depth) depth
  have scanned := batch_linear levels roots
  have rootBound : roots.length ≤ Fintype.card L := by
    have filter := List.length_filter_le (fun l => (matching.left l).isNone) vertices
    rw [BreadthSearch.vertices_length vertices nodup complete] at filter
    exact filter
  have bucketBound : (∑ l, (levels l).length) ≤ ∑ l, (buckets l).length :=
    Finset.sum_le_sum (fun l _ => level_length_le buckets matching _ depth l)
  have spec := blocking_spec levels roots
  have written := family_execute_cost matching (batch levels (Fintype.card L) roots initial).paths spec.disjoint
  change 10*(∑ l, (buckets l).length)+8*Fintype.card L+4*Fintype.card R+
    (batch levels (Fintype.card L) roots initial).cost+
    (executeRoutes matching (batch levels (Fintype.card L) roots initial).paths).2+5 ≤ _
  omega

theorem layers_above (buckets : L → List R) (matching : State L R) (lower : Nat)
    (short : NoShort buckets matching lower) (distance : L → Option Nat) (depth : Nat)
    (route : ∃ p : Route L R,
      Follows (levelBuckets buckets matching (BreadthSearch.height distance depth) depth) p ∧ matching.left p.first=none) : lower < depth := by
  obtain ⟨p,follows,free⟩ := route
  have alternating := level_follows_alternating buckets matching _ depth p follows
  have length := level_follows_length buckets matching _ depth p follows
  by_contra h
  exact short ⟨p,alternating,free,by omega⟩

end LeanTrominoes.BipartiteMatching
