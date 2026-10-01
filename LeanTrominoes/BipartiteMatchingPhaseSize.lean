/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingPhaseFamily
import LeanTrominoes.BipartiteMatchingBreadthInvariant

/-! # Nonempty blocking phases and finite vertex budgets -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

theorem blocking_nonempty (buckets : Buckets L R) (roots : List L)
    (route : ∃ p : Route L R, Follows buckets p ∧ p.first ∈ roots) :
    (batch buckets (Fintype.card L) roots initial).paths ≠ [] := by
  intro empty
  obtain ⟨p,follows,root⟩ := route
  have spec := blocking_spec buckets roots
  have unused : ∀ l ∈ p.vertices, (batch buckets (Fintype.card L) roots initial).state.used l=false := by
    intro l _
    cases h : (batch buckets (Fintype.card L) roots initial).state.used l with
    | false => rfl
    | true =>
      have impossible := (spec.used l).mp h
      rw [empty] at impossible
      simpa [initial] using impossible
  have hit := blocking_cut buckets roots p follows root unused
  have impossible := (spec.reserved p.target).mp hit
  rw [empty] at impossible
  simpa [initial] using impossible

theorem routes_length (paths : List (Route L R)) : paths.length ≤ (paths.flatMap Route.vertices).length := by
  induction paths with
  | nil => simp
  | cons p ps ih =>
    have positive : 0 < p.vertices.length := by cases p <;> simp [Route.vertices]
    simp only [List.flatMap_cons,List.length_cons,List.length_append]
    omega

theorem family_vertex_bound (paths : List (Route L R)) (nodup : (paths.flatMap Route.vertices).Nodup) :
    (paths.flatMap Route.vertices).length ≤ Fintype.card L := by
  rw [← List.toFinset_card_of_nodup nodup]
  exact Finset.card_le_univ _

theorem family_execute_cost (matching : State L R) (paths : List (Route L R))
    (nodup : (paths.flatMap Route.vertices).Nodup) : (executeRoutes matching paths).2 ≤ 20*Fintype.card L+1 := by
  have cost := executeRoutes_cost matching paths
  have nodes := family_vertex_bound paths nodup
  have count := routes_length paths
  omega

theorem free_size (matching : State L R) : (BreadthSearch.freeSet matching).card+size matching=Fintype.card L := by
  have partition : BreadthSearch.freeSet matching ∪ domain matching=Finset.univ := by
    ext l
    cases h : matching.left l <;> simp [BreadthSearch.freeSet,domain,h]
  have disjoint : Disjoint (BreadthSearch.freeSet matching) (domain matching) := by
    apply Finset.disjoint_left.mpr
    intro l free used
    cases h : matching.left l <;> simp_all [BreadthSearch.freeSet,domain]
  have count := Finset.card_union_of_disjoint disjoint
  rw [partition,Finset.card_univ] at count
  exact count.symm

theorem freeVertices_card (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (matching : State L R) : (BreadthSearch.freeVertices vertices matching).length=(BreadthSearch.freeSet matching).card := by
  have nd : (BreadthSearch.freeVertices vertices matching).Nodup := nodup.filter _
  have equal : (BreadthSearch.freeVertices vertices matching).toFinset=BreadthSearch.freeSet matching := by
    ext l
    cases h : matching.left l <;> simp [BreadthSearch.freeVertices,BreadthSearch.freeSet,h,complete]
  rw [← List.toFinset_card_of_nodup nd,equal]

end LeanTrominoes.BipartiteMatching
