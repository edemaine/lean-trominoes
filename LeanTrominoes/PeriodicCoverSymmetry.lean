/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicFiniteCoverReach
import LeanTrominoes.ImplicationGraphSatisfiability

/-! # Translation symmetry and the 2SAT criterion on the finite cover -/
namespace LeanTrominoes.PeriodicLatticeGraph
open ImplicationGraph
variable {V : Type*} {d : Nat}
def coverTranslate {M : Nat} (t : CoverLattice d M) (u : V × CoverLattice d M) := (u.1,u.2+t)

theorem cover_reach_translate (arcs : List (Arc V d)) (M : Nat) {u v : V × CoverLattice d M}
    (path : CoverReach arcs M u v) (t : CoverLattice d M) :
    CoverReach arcs M (coverTranslate t u) (coverTranslate t v) := by
  induction path with
  | refl => exact .refl
  | @tail w v path edge ih =>
    obtain ⟨e,he,source,target,equal⟩ := edge
    refine ih.tail ⟨e,he,source,target,?_⟩
    change v.2+t=(w.2+t)+wrap M e.offset
    rw [equal]
    abel

theorem cover_adj_skew (arcs : List (Arc V d)) (M : Nat) (neg : V → V) (skew : SkewArcs arcs neg)
    {u v : V × CoverLattice d M} (edge : CoverAdj arcs M u v) :
    CoverAdj arcs M (neg v.1,v.2) (neg u.1,u.2) := by
  obtain ⟨e,he,source,target,equal⟩ := edge
  refine ⟨skewArc neg e,skew e he,congrArg neg target,congrArg neg source,?_⟩
  change u.2=v.2+wrap M (-e.offset)
  have negative : wrap M (-e.offset) = -wrap M e.offset := by ext i; simp [wrap]
  rw [equal,negative]
  abel

def coverImplicationReach (arcs : List (Arc V d)) (M : Nat) (neg : V → V)
    (involutive : Function.Involutive neg) (skew : SkewArcs arcs neg) :
    SkewReach (V × CoverLattice d M) where
  neg := fun u => (neg u.1,u.2)
  involutive := by rintro ⟨v,z⟩; simp [involutive v]
  reach := CoverReach arcs M
  refl := fun _ => .refl
  trans := Relation.ReflTransGen.trans
  skew := by
    intro u v path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih => exact ih.head (cover_adj_skew arcs M neg skew edge)

/-- Translation symmetry reduces contradiction tests to one vertex per protovertex. -/
theorem cover_noContradiction_iff (arcs : List (Arc V d)) (M : Nat) (neg : V → V)
    (involutive : Function.Involutive neg) (skew : SkewArcs arcs neg) :
    (coverImplicationReach arcs M neg involutive skew).NoContradiction ↔
      ∀ a, ¬ (CoverReach arcs M (a,0) (neg a,0) ∧ CoverReach arcs M (neg a,0) (a,0)) := by
  constructor
  · intro all a
    exact all (a,0)
  · rintro zero ⟨a,z⟩ ⟨forward,backward⟩
    have one := cover_reach_translate arcs M forward (-z)
    have two := cover_reach_translate arcs M backward (-z)
    apply zero a
    constructor
    · simpa [coverTranslate,coverImplicationReach] using one
    · simpa [coverTranslate,coverImplicationReach] using two

theorem infinite_noContradiction_iff (arcs : List (Arc V d)) (neg : V → V)
    (involutive : Function.Involutive neg) (skew : SkewArcs arcs neg) :
    (implicationReach arcs neg involutive skew).NoContradiction ↔
      ∀ a, ¬ (Reach arcs (a,0) (neg a,0) ∧ Reach arcs (neg a,0) (a,0)) := by
  constructor
  · intro all a
    exact all (a,0)
  · rintro zero ⟨a,z⟩ ⟨forward,backward⟩
    have one := reach_translate arcs forward (-z)
    have two := reach_translate arcs backward (-z)
    apply zero a
    constructor
    · simpa [translate,implicationReach,opposite] using one
    · simpa [translate,implicationReach,opposite] using two

end LeanTrominoes.PeriodicLatticeGraph
