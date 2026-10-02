/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicLatticeGraph
import LeanTrominoes.SkewPeriodicReach
import LeanTrominoes.ImplicationGraphSatisfiability
import LeanTrominoes.FiniteReachFrontier

/-! # Translation and complement symmetry of periodic implication paths -/
namespace LeanTrominoes.PeriodicLatticeGraph
open ImplicationGraph
variable {V : Type*} {d : Nat}

def Reach (arcs : List (Arc V d)) := Relation.ReflTransGen (Adj arcs)
def QuotientAdj (arcs : List (Arc V d)) (u v : V) := ∃ e ∈ arcs, e.source=u ∧ e.target=v

theorem reach_translate (arcs : List (Arc V d)) {u v : V × Lattice d} (path : Reach arcs u v) (t : Lattice d) :
    Reach arcs (translate t u) (translate t v) := by
  induction path with
  | refl => exact .refl
  | @tail w v path edge ih => exact ih.tail (adj_translate arcs w v t edge)

def opposite (neg : V → V) (u : V × Lattice d) := (neg u.1,u.2)
def skewArc (neg : V → V) (e : Arc V d) : Arc V d := ⟨neg e.target,neg e.source,-e.offset⟩
def SkewArcs (arcs : List (Arc V d)) (neg : V → V) : Prop := ∀ e ∈ arcs, skewArc neg e ∈ arcs

theorem adj_skew (arcs : List (Arc V d)) (neg : V → V) (skew : SkewArcs arcs neg)
    {u v : V × Lattice d} (edge : Adj arcs u v) : Adj arcs (opposite neg v) (opposite neg u) := by
  obtain ⟨e,he,source,target,equal⟩ := edge
  refine ⟨skewArc neg e,skew e he,congrArg neg target,congrArg neg source,?_⟩
  change u.2=v.2+(-e.offset)
  rw [equal]
  abel

theorem reach_skew (arcs : List (Arc V d)) (neg : V → V) (skew : SkewArcs arcs neg)
    {u v : V × Lattice d} (path : Reach arcs u v) : Reach arcs (opposite neg v) (opposite neg u) := by
  induction path with
  | refl => exact .refl
  | @tail w v path edge ih => exact ih.head (adj_skew arcs neg skew edge)

/-- The abstract displacement-group lemmas apply to the actual infinite periodic graph. -/
def displacementReach (arcs : List (Arc V d)) (neg : V → V) (involutive : Function.Involutive neg)
    (skew : SkewArcs arcs neg) : SkewPeriodicReach V (Lattice d) where
  neg := neg
  involutive := involutive
  reach := fun u v z => Reach arcs (u,0) (v,z)
  refl := fun _ => .refl
  comp := by
    intro u v w x y first second
    have translated := reach_translate arcs second x
    have normalized : Reach arcs (v,x) (w,x+y) := by simpa [translate,add_comm] using translated
    exact first.trans normalized
  skew := by
    intro u v x path
    have reversed := reach_skew arcs neg skew path
    have translated := reach_translate arcs reversed (-x)
    simpa [translate,opposite] using translated

/-- The infinite graph itself has the skew reachability structure used by 2SAT. -/
def implicationReach (arcs : List (Arc V d)) (neg : V → V) (involutive : Function.Involutive neg)
    (skew : SkewArcs arcs neg) : SkewReach (V × Lattice d) where
  neg := opposite neg
  involutive := by rintro ⟨v,z⟩; simp [opposite,involutive v]
  reach := Reach arcs
  refl := fun _ => .refl
  trans := Relation.ReflTransGen.trans
  skew := reach_skew arcs neg skew

theorem quotient_reach (arcs : List (Arc V d)) {u v : V × Lattice d} (path : Reach arcs u v) :
    Relation.ReflTransGen (QuotientAdj arcs) u.1 v.1 := by
  induction path with
  | refl => exact .refl
  | @tail w v path edge ih =>
    obtain ⟨e,he,source,target,_⟩ := edge
    exact ih.tail ⟨e,he,source,target⟩

/-- A quotient path can be chosen with displacement at most |V| times the edge bound. -/
theorem bounded_quotient_lift [Fintype V] [DecidableEq V]
    (arcs : List (Arc V d)) (B : Nat) (locality : ∀ e ∈ arcs, ∀ i, (e.offset i).natAbs ≤ B)
    (u v : V) (path : Relation.ReflTransGen (QuotientAdj arcs) u v) :
    ∃ z, Reach arcs (u,0) (v,z) ∧ ∀ i, (z i).natAbs ≤ Fintype.card V*B := by
  classical
  let P := fun k v => ∃ z, Reach arcs (u,0) (v,z) ∧ ∀ i, (z i).natAbs ≤ k*B
  have base : P 0 u := ⟨0,.refl,by simp⟩
  have keep (k : Nat) (v : V) (h : P k v) : P (k+1) v := by
    obtain ⟨z,reach,bound⟩ := h
    refine ⟨z,reach,fun i => (bound i).trans ?_⟩
    exact Nat.mul_le_mul_right B (Nat.le_succ k)
  have step (k : Nat) (v w : V) (h : P k v) (edge : QuotientAdj arcs v w) : P (k+1) w := by
    obtain ⟨z,reach,bound⟩ := h
    obtain ⟨e,he,source,target⟩ := edge
    refine ⟨z+e.offset,reach.tail ⟨e,he,source,target,rfl⟩,?_⟩
    intro i
    have triangle := Int.natAbs_add_le (z i) (e.offset i)
    have one := bound i
    have two := locality e he i
    change (z i+e.offset i).natAbs ≤ (k+1)*B
    simp only [Nat.add_mul,one_mul]
    omega
  exact frontier_induction (QuotientAdj arcs) u P base keep step _ v
    (reachable_mem_frontier (QuotientAdj arcs) u v path)

end LeanTrominoes.PeriodicLatticeGraph
