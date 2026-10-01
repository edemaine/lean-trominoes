/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingFamilyValues
import LeanTrominoes.BipartiteMatchingLayers
import LeanTrominoes.BlockingPathBatchSemantics

/-! # Matching and label invariants for a complete shortest-path family -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

structure PhaseFamily (buckets : L → List R) (matching : State L R) (height : L → Nat)
    (depth : Nat) (paths : List (Route L R)) : Prop where
  follows : ∀ p ∈ paths, Follows (levelBuckets buckets matching height depth) p
  free : ∀ p ∈ paths, matching.left p.first=none
  vertices : (paths.flatMap Route.vertices).Nodup
  targets : (paths.map Route.target).Nodup

namespace PhaseFamily
variable {buckets : L → List R} {matching : State L R} {height : L → Nat} {depth : Nat}
  {paths : List (Route L R)} (family : PhaseFamily buckets matching height depth paths)
include family

theorem alternating : ∀ p ∈ paths, Alternating (fun l r => r ∈ buckets l) matching p :=
  fun p hp => level_follows_alternating buckets matching height depth p (family.follows p hp)

theorem labels_nodup : (paths.flatMap routeLabels).Nodup :=
  family_labels_nodup _ matching paths family.alternating family.vertices family.targets

theorem correct (consistent : Consistent matching) (supported : Supported (fun l r => r ∈ buckets l) matching) :
    Consistent (applyRoutes matching paths) ∧ Supported (fun l r => r ∈ buckets l) (applyRoutes matching paths) ∧
      size (applyRoutes matching paths)=size matching+paths.length :=
  applyRoutes_correct _ matching paths consistent supported family.alternating family.free family.vertices family.labels_nodup

theorem new_free (l : L) (free : (applyRoutes matching paths).left l=none) :
    l ∉ paths.flatMap Route.vertices ∧ matching.left l=none := by
  have outside : l ∉ paths.flatMap Route.vertices := by
    intro member
    obtain ⟨p,hp,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨r,pair⟩ := pair_at_vertex p l inside
    have written := applyRoutes_left_write matching paths family.vertices p hp l r pair
    simp_all
  exact ⟨outside,by rwa [applyRoutes_left_outside matching paths l outside] at free⟩

theorem new_free_right (r : R) (free : (applyRoutes matching paths).right r=none) :
    r ∉ paths.flatMap routeLabels ∧ matching.right r=none := by
  have outside : r ∉ paths.flatMap routeLabels := by
    intro member
    obtain ⟨p,hp,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨l,pair⟩ := pair_at_label p r inside
    have written := applyRoutes_right_write matching paths family.labels_nodup p hp l r pair
    simp_all
  exact ⟨outside,by rwa [applyRoutes_right_outside matching paths r outside] at free⟩

/-- Newly reversed matching arcs go down in the old level labels. -/
theorem pair_down (labels : Labels buckets matching height depth) (p : Route L R) (hp : p ∈ paths)
    (l : L) (r : R) (pair : (l,r) ∈ routePairs p) (v : L) (edge : r ∈ buckets v) : height l ≤ height v := by
  have selected := (level_pairs buckets matching height depth p (family.follows p hp) l r pair).2
  have bound := labels.arc v r edge
  cases mate : matching.right r <;> simp only [mate] at selected bound <;> omega

theorem labels_final (labels : Labels buckets matching height depth) :
    Labels buckets (applyRoutes matching paths) height depth := by
  refine ⟨?_,?_⟩
  · intro l free
    exact labels.free l (family.new_free l free).2
  · intro v r edge
    by_cases inside : r ∈ paths.flatMap routeLabels
    · obtain ⟨p,hp,member⟩ := List.mem_flatMap.mp inside
      obtain ⟨l,pair⟩ := pair_at_label p r member
      have written := applyRoutes_right_write matching paths family.labels_nodup p hp l r pair
      rw [written]
      exact (family.pair_down labels p hp l r pair v edge).trans (Nat.le_succ _)
    · rw [applyRoutes_right_outside matching paths r inside]
      exact labels.arc v r edge

theorem used_partner (consistent : Consistent (applyRoutes matching paths)) (l : L)
    (inside : l ∈ paths.flatMap Route.vertices) (r : R) (mate : (applyRoutes matching paths).right r=some l) :
    r ∈ paths.flatMap routeLabels := by
  obtain ⟨p,hp,member⟩ := List.mem_flatMap.mp inside
  obtain ⟨t,pair⟩ := pair_at_vertex p l member
  have written := applyRoutes_left_write matching paths family.vertices p hp l t pair
  have old := (consistent l r).mpr mate
  have equal : t=r := Option.some.inj (written.symm.trans old)
  subst t
  exact List.mem_flatMap.mpr ⟨p,hp,by rw [← routePairs_snd]; exact List.mem_map.mpr ⟨(l,r),pair,rfl⟩⟩

end PhaseFamily

/-- A batch of level-graph routes satisfies the family invariant. -/
theorem blocking_family (buckets : L → List R) (matching : State L R) (height : L → Nat) (depth : Nat)
    (roots : List L) (free : ∀ l ∈ roots, matching.left l=none) :
    PhaseFamily buckets matching height depth
      (batch (levelBuckets buckets matching height depth) (Fintype.card L) roots initial).paths := by
  have spec := blocking_spec (levelBuckets buckets matching height depth) roots
  exact ⟨spec.follows,fun p hp => free p.first (spec.root p hp),spec.disjoint,spec.distinctTargets⟩

end LeanTrominoes.BipartiteMatching
