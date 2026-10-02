/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingSolverCorrect

/-! # A short simple augmenting route in the finite quotient -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

theorem short_route (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (matching : State L R) (consistent : Consistent matching)
    (perfect : HasFiniteMatching buckets) (imperfect : ¬ Full matching) :
    ∃ p : Route L R, Alternating (fun l r => r ∈ buckets l) matching p ∧
      matching.left p.first=none ∧ p.vertices.Nodup ∧ (routeLabels p).Nodup ∧
      2*p.vertices.length-1 < Fintype.card L+Fintype.card R := by
  have positive : 0 < (BreadthSearch.freeVertices vertices matching).length := by
    by_contra h
    have nil : BreadthSearch.freeVertices vertices matching=[] := List.length_eq_zero_iff.mp (by omega)
    exact imperfect (roots_empty_full vertices complete matching (by simp [nil]))
  have spec := BreadthSearch.search_spec vertices nodup complete buckets matching consistent positive
  cases found : BreadthSearch.search vertices buckets matching with
  | exhausted cost => simp only [found,BreadthSearch.Spec] at spec
  | deficient distance depth cost =>
    simp only [found,BreadthSearch.Spec] at spec
    obtain ⟨f,edges⟩ := perfect
    have hall := hall_of_equiv buckets f edges (BreadthSearch.prefixSet distance depth)
    omega
  | layers distance depth cost =>
    simp only [found,BreadthSearch.Spec] at spec
    obtain ⟨labels,density,depthPositive,route⟩ := spec
    let levels := levelBuckets buckets matching (BreadthSearch.height distance depth) depth
    let roots := BreadthSearch.freeVertices vertices matching
    have nonempty := blocking_nonempty levels roots (by
      obtain ⟨p,hp,free⟩ := route
      exact ⟨p,hp,(free_mem vertices matching p.first).mpr ⟨complete p.first,free⟩⟩)
    obtain ⟨p,member⟩ := List.exists_mem_of_ne_nil _ nonempty
    have batchSpec := blocking_spec levels roots
    have alternating := level_follows_alternating buckets matching _ depth p (batchSpec.follows p member)
    have free := (free_mem vertices matching p.first).mp (batchSpec.root p member) |>.2
    have simple := batchSpec.simple p member
    have length : p.vertices.length ≤ Fintype.card L := by
      rw [← List.toFinset_card_of_nodup simple]
      exact Finset.card_le_univ _
    obtain ⟨f,_⟩ := perfect
    have balanced := Fintype.card_congr f
    have nonzero : 0 < p.vertices.length := by cases p <;> simp [Route.vertices]
    exact ⟨p,alternating,free,simple,labels_nodup _ matching p alternating simple,by omega⟩

end LeanTrominoes.BipartiteMatching
