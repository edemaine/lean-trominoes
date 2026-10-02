/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicAugmentingLift
import LeanTrominoes.BipartiteMatchingShortRoute

/-! # Lemma 4.5: a protovertex-simple augmenting path of length less than |V| -/
namespace LeanTrominoes.PeriodicBipartite
open BipartiteMatching BlockingPath
variable {L R : Type*} {d : Nat} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

structure ShortAugmentingPath {edges : List (Edge L R d)} (matching : PeriodOnePartial edges) where
  route : Route (L × Lattice d) (R × Lattice d)
  alternating : Alternating (Adj edges) matching.partners route
  free : matching.partners.left route.first=none
  protoSimple : (route.map Prod.fst Prod.fst).allVertices.Nodup
  length : route.allVertices.length-1 < Fintype.card L+Fintype.card R

/-- The quotient is full exactly when the infinite period-one matching is full. -/
theorem PeriodOnePartial.full_iff {edges : List (Edge L R d)} (matching : PeriodOnePartial edges) :
    Full matching.quotient ↔ Full matching.partners := by
  constructor
  · intro full u
    obtain ⟨l,z⟩ := u
    rw [matching.left_at]
    simpa using full l
  · intro full l free
    have lifted := matching.left_free l free 0
    exact full (l,0) lifted

/-- Applies to an arbitrary translation-covariant partial matching, in every dimension. -/
theorem short_augmenting_path (edges : List (Edge L R d)) (perfect : HasPerfectMatching edges)
    (matching : PeriodOnePartial edges) (imperfect : ¬ Full matching.partners) :
    Nonempty (ShortAugmentingPath matching) := by
  classical
  let vertices := (Finset.univ : Finset L).toList
  have nodup : vertices.Nodup := Finset.nodup_toList _
  have complete : ∀ l, l ∈ vertices := by intro l; simp [vertices]
  have quotientPerfect := (finite_iff_quotient edges).mpr ((perfect_iff_quotient edges).mp perfect)
  have quotientImperfect : ¬ Full matching.quotient := fun full => imperfect (matching.full_iff.mp full)
  obtain ⟨p,alternating,free,leftSimple,rightSimple,length⟩ := short_route vertices nodup complete
    (buckets edges) matching.quotient matching.quotient_consistent quotientPerfect quotientImperfect
  have alt : Alternating (QuotientAdj edges) matching.quotient p := by
    simpa only [buckets_mem] using alternating
  obtain ⟨q,lifted,first,project⟩ := matching.lift_route p alt 0
  have sameLength : q.vertices.length=p.vertices.length := by
    have mapLength := congrArg (fun r => r.vertices.length) project
    simpa only [Route.map_vertices,List.length_map] using mapLength
  refine ⟨⟨q,lifted,?_,?_,?_⟩⟩
  · rw [first]
    exact matching.left_free p.first free 0
  · rw [project]
    exact p.allVertices_nodup leftSimple rightSimple
  · rw [Route.allVertices_length,sameLength]
    exact length

end LeanTrominoes.PeriodicBipartite
