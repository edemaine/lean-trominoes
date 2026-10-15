/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Tactic

/-! # Displacement groups in self-dual implication components -/
namespace LeanTrominoes.ImplicationGraph
variable {V G : Type*} [AddCommGroup G]

structure SkewPeriodicReach (V G : Type*) [AddCommGroup G] where
  neg : V → V
  involutive : Function.Involutive neg
  reach : V → V → G → Prop
  refl : ∀ v, reach v v 0
  comp : ∀ {u v w x y}, reach u v x → reach v w y → reach u w (x+y)
  skew : ∀ {u v x}, reach u v x → reach (neg v) (neg u) (-x)

namespace SkewPeriodicReach
variable (R : SkewPeriodicReach V G)
variable {a : V} {x y : G}

/-- Complementing and reversing a path between opposite literals preserves its orientation. -/
theorem cross_neg (path : R.reach a (R.neg a) x) : R.reach a (R.neg a) (-x) := by
  simpa only [R.involutive a] using R.skew path

theorem return_neg (path : R.reach (R.neg a) a y) : R.reach (R.neg a) a (-y) := by
  simpa only [R.involutive a] using R.skew path

/-- Closed-walk displacements in a self-dual component are closed under negation. -/
theorem closed_neg (forward : R.reach a (R.neg a) x) (backward : R.reach (R.neg a) a y)
    {c : G} (closed : R.reach a a c) : R.reach a a (-c) := by
  have inverseBridge := R.comp (R.cross_neg forward) (R.return_neg backward)
  have path := R.comp (R.comp (R.comp forward (R.skew closed)) backward) inverseBridge
  convert path using 1 <;> abel

/-- The closed-walk monoid is an additive group; no undirectedness is assumed. -/
def displacementGroup (forward : R.reach a (R.neg a) x) (backward : R.reach (R.neg a) a y) : AddSubgroup G where
  carrier := {c | R.reach a a c}
  zero_mem' := R.refl a
  add_mem' := fun p q => R.comp p q
  neg_mem' := R.closed_neg forward backward

@[simp] theorem mem_displacementGroup (forward : R.reach a (R.neg a) x)
    (backward : R.reach (R.neg a) a y) (c : G) :
    c ∈ R.displacementGroup forward backward ↔ R.reach a a c := Iff.rfl

/-- Every path between opposite literals has displacement of order at most two modulo the group. -/
theorem twice_cross (forward : R.reach a (R.neg a) x) (backward : R.reach (R.neg a) a y) :
    x+x ∈ R.displacementGroup forward backward := by
  have one := R.comp forward backward
  have two := R.comp forward (R.return_neg backward)
  have path := R.comp one two
  change R.reach a a (x+x)
  convert path using 1 <;> abel

/-- Path displacements form a coset whenever the endpoints are in a self-dual component. -/
theorem reach_iff_coset (forward : R.reach a (R.neg a) x) (backward : R.reach (R.neg a) a y)
    {b : V} {p q z : G} (chosen : R.reach a b p) (returnPath : R.reach b a q) :
    R.reach a b z ↔ z-p ∈ R.displacementGroup forward backward := by
  constructor
  · intro path
    have cycle := R.comp chosen returnPath
    have other := R.comp path returnPath
    have difference := R.comp other (R.closed_neg forward backward cycle)
    change R.reach a a (z-p)
    convert difference using 1 <;> abel
  · intro cycle
    have path := R.comp cycle chosen
    convert path using 1 <;> abel

/-- At the original translate, one direction of a contradiction forces the other. -/
theorem contradiction_iff (forward : R.reach a (R.neg a) x) (backward : R.reach (R.neg a) a y) :
    (R.reach a (R.neg a) 0 ∧ R.reach (R.neg a) a 0) ↔ x ∈ R.displacementGroup forward backward := by
  constructor
  · intro paths
    have cycle := (R.reach_iff_coset forward backward forward backward).mp paths.1
    have inverse := (R.displacementGroup forward backward).neg_mem cycle
    simpa using inverse
  · intro member
    have inverse := (R.displacementGroup forward backward).neg_mem member
    have first : R.reach a (R.neg a) 0 :=
      (R.reach_iff_coset forward backward forward backward).mpr (by simpa using inverse)
    refine ⟨first,?_⟩
    have path := R.comp (R.return_neg backward) (R.comp first backward)
    convert path using 1 <;> abel

end SkewPeriodicReach
end LeanTrominoes.ImplicationGraph
