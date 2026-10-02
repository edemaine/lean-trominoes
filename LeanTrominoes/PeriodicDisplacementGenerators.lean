/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicImplicationReach
import LeanTrominoes.LatticeBoundedFrame
import LeanTrominoes.LatticeDeterminantBound

/-! # Bounded generators for a self-dual implication component's displacement group -/
namespace LeanTrominoes.PeriodicLatticeGraph
open ImplicationGraph
variable {V : Type*} {d : Nat}

def Component (arcs : List (Arc V d)) (root v : V) : Prop :=
  Relation.ReflTransGen (QuotientAdj arcs) root v ∧ Relation.ReflTransGen (QuotientAdj arcs) v root

def Residuals (arcs : List (Arc V d)) (root : V) (potential : V → Lattice d) : Set (Lattice d) :=
  {c | ∃ e ∈ arcs, Component arcs root e.source ∧ Component arcs root e.target ∧
    c=potential e.source+e.offset-potential e.target}

/-- Fundamental edge residuals generate exactly the closed-walk displacement group. -/
theorem displacement_generated (arcs : List (Arc V d)) (neg : V → V) (involutive : Function.Involutive neg)
    (skew : SkewArcs arcs neg) (root : V) (x y : Lattice d)
    (forward : Reach arcs (root,0) (neg root,x)) (backward : Reach arcs (neg root,0) (root,y))
    (potential : V → Lattice d)
    (paths : ∀ v, Component arcs root v → Reach arcs (root,0) (v,potential v))
    (returns : ∀ v, Component arcs root v → ∃ z, Reach arcs (v,0) (root,z)) :
    (displacementReach arcs neg involutive skew).displacementGroup forward backward =
      AddSubgroup.closure (Residuals arcs root potential) := by
  let R := displacementReach arcs neg involutive skew
  let H := R.displacementGroup forward backward
  let K := AddSubgroup.closure (Residuals arcs root potential)
  have residual_mem (e : Arc V d) (he : e ∈ arcs) (source : Component arcs root e.source)
      (target : Component arcs root e.target) : potential e.source+e.offset-potential e.target ∈ H := by
    obtain ⟨q,back⟩ := returns e.target target
    have edge : R.reach e.source e.target e.offset := by
      apply Relation.ReflTransGen.single
      exact ⟨e,he,rfl,rfl,by simp⟩
    have one : potential e.source+e.offset+q ∈ H := R.comp (R.comp (paths e.source source) edge) back
    have two : potential e.target+q ∈ H := R.comp (paths e.target target) back
    have difference := H.sub_mem one two
    convert difference using 1 <;> abel
  have K_le : K ≤ H := by
    apply (AddSubgroup.closure_le H).mpr
    rintro c ⟨e,he,source,target,rfl⟩
    exact residual_mem e he source target
  have generated : ∀ u : V × Lattice d, Reach arcs (root,0) u →
      Relation.ReflTransGen (QuotientAdj arcs) u.1 root → u.2+potential root-potential u.1 ∈ K := by
    intro u path
    induction path with
    | refl =>
      intro back
      simpa using K.zero_mem
    | @tail w v path edge ih =>
      intro back
      obtain ⟨e,he,source,target,equal⟩ := edge
      have projected : QuotientAdj arcs w.1 v.1 := ⟨e,he,source,target⟩
      have wBack := back.head projected
      have wComponent : Component arcs root w.1 := ⟨quotient_reach arcs path,wBack⟩
      have vComponent : Component arcs root v.1 := ⟨(quotient_reach arcs path).tail projected,back⟩
      have eSource : Component arcs root e.source := source.symm ▸ wComponent
      have eTarget : Component arcs root e.target := target.symm ▸ vComponent
      have edgeMember : potential w.1+e.offset-potential v.1 ∈ K := by
        apply AddSubgroup.subset_closure
        exact ⟨e,he,eSource,eTarget,by rw [source,target]⟩
      have sum := K.add_mem (ih wBack) edgeMember
      rw [equal]
      convert sum using 1 <;> abel
  apply le_antisymm
  · intro c hc
    have member := generated (root,c) hc .refl
    simpa using member
  · exact K_le

/-- All these residuals have coordinates bounded by (2|V|+1) times the arc bound. -/
theorem residual_bound [Fintype V] (arcs : List (Arc V d)) (root : V) (potential : V → Lattice d)
    (B : Nat) (locality : ∀ e ∈ arcs, ∀ i, (e.offset i).natAbs ≤ B)
    (bounded : ∀ v, Component arcs root v → ∀ i, (potential v i).natAbs ≤ Fintype.card V*B) :
    ∀ c ∈ Residuals arcs root potential, ∀ i, (c i).natAbs ≤ (2*Fintype.card V+1)*B := by
  rintro c ⟨e,he,source,target,rfl⟩ i
  have first := bounded e.source source i
  have last := bounded e.target target i
  have middle := locality e he i
  have sum := Int.natAbs_add_le (potential e.source i) (e.offset i)
  have difference := Int.natAbs_sub_le (potential e.source i+e.offset i) (potential e.target i)
  change (potential e.source i+e.offset i-potential e.target i).natAbs ≤ _
  have expand : (2*Fintype.card V+1)*B=Fintype.card V*B+B+Fintype.card V*B := by ring
  rw [expand]
  omega

/-- Each component supplies a small nonzero multiplier of its saturation lattice. -/
theorem bounded_displacement_saturation [Fintype V] [DecidableEq V]
    (arcs : List (Arc V d)) (neg : V → V) (involutive : Function.Involutive neg)
    (skew : SkewArcs arcs neg) (B : Nat) (locality : ∀ e ∈ arcs, ∀ i, (e.offset i).natAbs ≤ B)
    (root : V) (x y : Lattice d) (forward : Reach arcs (root,0) (neg root,x))
    (backward : Reach arcs (neg root,0) (root,y)) :
    ∃ delta : Int, delta ≠ 0 ∧ delta.natAbs ≤ d.factorial*((2*Fintype.card V+1)*B+1)^d ∧
      ∀ (z : Lattice d) (c : Int), c ≠ 0 →
        c • z ∈ (displacementReach arcs neg involutive skew).displacementGroup forward backward →
        delta • z ∈ (displacementReach arcs neg involutive skew).displacementGroup forward backward := by
  classical
  have choosePotential (v : V) : ∃ z, Component arcs root v →
      Reach arcs (root,0) (v,z) ∧ ∀ i, (z i).natAbs ≤ Fintype.card V*B := by
    by_cases component : Component arcs root v
    · obtain ⟨z,path,bound⟩ := bounded_quotient_lift arcs B locality root v component.1
      exact ⟨z,fun _ => ⟨path,bound⟩⟩
    · exact ⟨0,fun h => False.elim (component h)⟩
  choose potential potential_spec using choosePotential
  have returns (v : V) (component : Component arcs root v) : ∃ z, Reach arcs (v,0) (root,z) := by
    obtain ⟨z,path,_⟩ := bounded_quotient_lift arcs B locality v root component.2
    exact ⟨z,path⟩
  have generated := displacement_generated arcs neg involutive skew root x y forward backward potential
    (fun v hv => (potential_spec v hv).1) returns
  have bound := residual_bound arcs root potential B locality (fun v hv => (potential_spec v hv).2)
  obtain ⟨frame,entries⟩ := bounded_frame (Residuals arcs root potential) ((2*Fintype.card V+1)*B+1)
    (by omega) (fun c hc i => (bound c hc i).trans (by omega))
  refine ⟨frame.matrix.det,frame.nonzero,determinant_bound frame.matrix _ entries,?_⟩
  rw [generated]
  exact frame.saturation

end LeanTrominoes.PeriodicLatticeGraph
