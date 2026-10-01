/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingAugmentFamily

/-! # Exact array values and the linear charge of family rewiring -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

theorem applyRoutes_left_outside (s : State L R) (paths : List (Route L R)) (l : L)
    (outside : l ∉ paths.flatMap Route.vertices) : (applyRoutes s paths).left l=s.left l := by
  induction paths generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have split : l ∉ p.vertices ∧ l ∉ ps.flatMap Route.vertices := by simpa using outside
    rw [applyRoutes,ih _ split.2,applyRoute_left_outside s p l split.1]

theorem applyRoutes_right_outside (s : State L R) (paths : List (Route L R)) (r : R)
    (outside : r ∉ paths.flatMap routeLabels) : (applyRoutes s paths).right r=s.right r := by
  induction paths generalizing s with
  | nil => rfl
  | cons p ps ih =>
    have split : r ∉ routeLabels p ∧ r ∉ ps.flatMap routeLabels := by simpa using outside
    rw [applyRoutes,ih _ split.2,applyRoute_right_outside s p r split.1]

theorem applyRoutes_left_write (s : State L R) (paths : List (Route L R))
    (nodup : (paths.flatMap Route.vertices).Nodup) (p : Route L R) (member : p ∈ paths)
    (l : L) (r : R) (pair : (l,r) ∈ routePairs p) : (applyRoutes s paths).left l=some r := by
  induction paths generalizing s with
  | nil => simp at member
  | cons q qs ih =>
    have split := List.nodup_append.mp nodup
    rcases List.mem_cons.mp member with equal | member
    · subst p
      have inside : l ∈ q.vertices := by rw [← routePairs_fst]; exact List.mem_map.mpr ⟨(l,r),pair,rfl⟩
      have outside : l ∉ qs.flatMap Route.vertices := by
        intro tail
        exact split.2.2 l inside l tail rfl
      rw [applyRoutes,applyRoutes_left_outside _ qs l outside]
      exact applyRoute_left_write s q split.1 l r pair
    · exact ih (applyRoute s q) split.2.1 member

theorem applyRoutes_right_write (s : State L R) (paths : List (Route L R))
    (nodup : (paths.flatMap routeLabels).Nodup) (p : Route L R) (member : p ∈ paths)
    (l : L) (r : R) (pair : (l,r) ∈ routePairs p) : (applyRoutes s paths).right r=some l := by
  induction paths generalizing s with
  | nil => simp at member
  | cons q qs ih =>
    have split := List.nodup_append.mp nodup
    rcases List.mem_cons.mp member with equal | member
    · subst p
      have inside : r ∈ routeLabels q := by rw [← routePairs_snd]; exact List.mem_map.mpr ⟨(l,r),pair,rfl⟩
      have outside : r ∉ qs.flatMap routeLabels := by
        intro tail
        exact split.2.2 r inside r tail rfl
      rw [applyRoutes,applyRoutes_right_outside _ qs r outside]
      exact applyRoute_right_write s q split.1 l r pair
    · exact ih (applyRoute s q) split.2.1 member

theorem pair_at_vertex (p : Route L R) (l : L) (member : l ∈ p.vertices) : ∃ r, (l,r) ∈ routePairs p := by
  rw [← routePairs_fst] at member
  obtain ⟨pair,inside,equal⟩ := List.mem_map.mp member
  obtain ⟨a,r⟩ := pair
  change a=l at equal
  subst a
  exact ⟨r,inside⟩

theorem pair_at_label (p : Route L R) (r : R) (member : r ∈ routeLabels p) : ∃ l, (l,r) ∈ routePairs p := by
  rw [← routePairs_snd] at member
  obtain ⟨pair,inside,equal⟩ := List.mem_map.mp member
  obtain ⟨l,t⟩ := pair
  change t=r at equal
  subst t
  exact ⟨l,inside⟩

def executeRoutes (s : State L R) : List (Route L R) → State L R × Nat
  | [] => (s,1)
  | p::ps =>
    let first := executeRoute s p
    let later := executeRoutes first.1 ps
    (later.1,4+first.2+later.2)

theorem executeRoutes_state (s : State L R) (paths : List (Route L R)) :
    (executeRoutes s paths).1=applyRoutes s paths := by
  induction paths generalizing s <;> simp_all [executeRoutes,executeRoute_state,applyRoutes]

theorem executeRoutes_cost (s : State L R) (paths : List (Route L R)) :
    (executeRoutes s paths).2 ≤ 16*(paths.flatMap Route.vertices).length+4*paths.length+1 := by
  induction paths generalizing s with
  | nil => simp [executeRoutes]
  | cons p ps ih =>
    have first := executeRoute_cost s p
    have later := ih (executeRoute s p).1
    simp only [executeRoutes,List.flatMap_cons,List.length_append,List.length_cons]
    omega

end LeanTrominoes.BipartiteMatching
