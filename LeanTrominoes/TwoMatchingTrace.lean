/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-! # Simple alternating traces in the union of two matchings

Follow a perfect matching, then a partial matching, from a free vertex.
The resulting trace cannot intersect itself. This does not require the
ambient graph to be bipartite.
-/
namespace LeanTrominoes.TwoMatching
variable {X : Type*}

structure PartialMatching (X : Type*) where
  mate : X → Option X
  symmetric : ∀ x y, mate x = some y → mate y = some x
  irreflexive : ∀ x, mate x ≠ some x

structure PerfectMatching (X : Type*) where
  mate : X → X
  involutive : Function.Involutive mate
  irreflexive : ∀ x, mate x ≠ x

variable (m : PartialMatching X) (p : PerfectMatching X)

inductive Trace (root : X) : X → Type _ where
  | start : Trace root root
  | step {x : X} (previous : Trace root x) (y : X)
      (paired : m.mate (p.mate x) = some y) : Trace root y

def Trace.endpoint {root x : X} (_t : Trace m p root x) : X := x

def Trace.vertices {root x : X} : Trace m p root x → List X
  | .start => [root]
  | .step previous y _ => previous.vertices ++ [p.mate previous.endpoint,y]

structure Invariant {root x : X} (t : Trace m p root x) : Prop where
  simple : t.vertices.Nodup
  root_mem : root ∈ t.vertices
  last_mem : x ∈ t.vertices
  perfect_closed : ∀ a ∈ t.vertices, a ≠ x → p.mate a ∈ t.vertices
  perfect_fresh : p.mate x ∉ t.vertices
  partial_closed : ∀ a ∈ t.vertices, a ≠ root →
    ∃ b ∈ t.vertices, m.mate a = some b

variable {m p}

theorem Trace.invariant {root x : X} (t : Trace m p root x)
    (free : m.mate root = none) : Invariant m p t := by
  classical
  induction t with
  | start =>
    refine ⟨by simp [vertices,endpoint],by simp [vertices,endpoint],by simp [vertices,endpoint],?_,?_,?_⟩
    · intro a ha h; simp only [vertices,endpoint,List.mem_singleton] at ha; exact (h ha).elim
    · simpa [vertices,endpoint] using p.irreflexive root
    · intro a ha h; simp only [vertices,endpoint,List.mem_singleton] at ha; exact (h ha).elim
  | @step x previous y paired ih =>
    have reverse := m.symmetric _ _ paired
    have y_fresh : y ∉ previous.vertices := by
      intro hy
      by_cases eq : y = root
      · subst y; rw [free] at reverse; contradiction
      · obtain ⟨b,hb,he⟩ := ih.partial_closed y hy eq
        have eq : b = p.mate x := Option.some.inj (he.symm.trans reverse)
        exact ih.perfect_fresh (eq ▸ hb)
    have distinct : p.mate x ≠ y := by
      intro eq; rw [← eq] at paired; exact m.irreflexive _ paired
    have p_y_fresh : p.mate y ∉ previous.vertices ++ [p.mate x,y] := by
      intro member
      rcases List.mem_append.mp member with old | new
      · by_cases eq : p.mate y = x
        · have y_eq : y = p.mate x := by rw [← eq,p.involutive]
          exact distinct y_eq.symm
        · have oldmate := ih.perfect_closed (p.mate y) old eq
          rw [p.involutive] at oldmate
          exact y_fresh oldmate
      · simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at new
        rcases new with eq | eq
        · have y_eq := p.involutive.injective eq
          exact y_fresh (y_eq ▸ ih.last_mem)
        · exact p.irreflexive y eq
    refine ⟨?_,?_,?_,?_,p_y_fresh,?_⟩
    · simp only [vertices,endpoint,List.nodup_append,List.nodup_cons,List.nodup_singleton,
        List.mem_singleton]
      refine ⟨ih.simple,by simpa using distinct,?_⟩
      intro a ha b hb eq
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
      rcases hb with rfl | rfl
      · exact ih.perfect_fresh (eq ▸ ha)
      · exact y_fresh (eq ▸ ha)
    · exact List.mem_append_left _ ih.root_mem
    · simp [vertices,endpoint]
    · intro a ha ne
      rcases List.mem_append.mp ha with old | new
      · by_cases eq : a = x
        · subst a; simp [vertices,endpoint]
        · exact List.mem_append_left _ (ih.perfect_closed a old eq)
      · simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at new
        rcases new with rfl | rfl
        · rw [p.involutive]; exact List.mem_append_left _ ih.last_mem
        · exact (ne rfl).elim
    · intro a ha ne
      rcases List.mem_append.mp ha with old | new
      · obtain ⟨b,hb,he⟩ := ih.partial_closed a old ne
        exact ⟨b,List.mem_append_left _ hb,he⟩
      · simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at new
        rcases new with rfl | rfl
        · exact ⟨y,by simp [vertices,endpoint],paired⟩
        · exact ⟨p.mate x,by simp [vertices,endpoint],reverse⟩

/-- Finishing at a free perfect-matching partner gives a simple augmenting path. -/
theorem Trace.finish_simple {root x : X} (t : Trace m p root x)
    (free : m.mate root = none) : (t.vertices ++ [p.mate x]).Nodup := by
  classical
  have inv := t.invariant free
  apply List.nodup_append.mpr
  refine ⟨inv.simple,by simp,?_⟩
  intro a ha b hb eq
  simp only [List.mem_singleton] at hb
  exact inv.perfect_fresh ((eq.trans hb) ▸ ha)

end LeanTrominoes.TwoMatching
