/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicImplicationReach
import Mathlib.Data.ZMod.Basic

/-! # Projecting and lifting paths in a finite lattice cover -/
namespace LeanTrominoes.PeriodicLatticeGraph
variable {V : Type*} {d : Nat}
abbrev CoverLattice (d M : Nat) := Fin d → ZMod M

def wrap (M : Nat) (z : Lattice d) : CoverLattice d M := fun i => z i

def CoverAdj (arcs : List (Arc V d)) (M : Nat) (u v : V × CoverLattice d M) : Prop :=
  ∃ e ∈ arcs, e.source=u.1 ∧ e.target=v.1 ∧ v.2=u.2+wrap M e.offset

def CoverReach (arcs : List (Arc V d)) (M : Nat) := Relation.ReflTransGen (CoverAdj arcs M)

@[simp] theorem wrap_add (M : Nat) (z t : Lattice d) : wrap M (z+t)=wrap M z+wrap M t := by
  ext i
  simp [wrap]
@[simp] theorem wrap_zero (M : Nat) : wrap M (0 : Lattice d)=0 := by ext i; simp [wrap]

/-- Every path in the infinite graph projects to the finite cover. -/
theorem reach_wrap (arcs : List (Arc V d)) (M : Nat) {u v : V × Lattice d} (path : Reach arcs u v) :
    CoverReach arcs M (u.1,wrap M u.2) (v.1,wrap M v.2) := by
  induction path with
  | refl => exact .refl
  | @tail w v path edge ih =>
    obtain ⟨e,he,source,target,equal⟩ := edge
    refine ih.tail ⟨e,he,source,target,?_⟩
    rw [equal,wrap_add]

/-- Every finite-cover path lifts from any specified integer representative of its start. -/
theorem cover_reach_lift (arcs : List (Arc V d)) (M : Nat) {u v : V × CoverLattice d M}
    (path : CoverReach arcs M u v) (z : Lattice d) (start : wrap M z=u.2) :
    ∃ t, Reach arcs (u.1,z) (v.1,t) ∧ wrap M t=v.2 := by
  induction path with
  | refl => exact ⟨z,.refl,start⟩
  | @tail w v path edge ih =>
    obtain ⟨t,lifted,equal⟩ := ih
    obtain ⟨e,he,source,target,displacement⟩ := edge
    refine ⟨t+e.offset,lifted.tail ⟨e,he,source,target,rfl⟩,?_⟩
    rw [wrap_add,equal,displacement]

/-- A lift returns to zero in the cover exactly when its displacement is a multiple of M. -/
theorem wrap_eq_zero_iff (M : Nat) (z : Lattice d) : wrap M z=0 ↔ ∃ t : Lattice d, z=M • t := by
  constructor
  · intro zero
    have divisible (i : Fin d) : (M : Int) ∣ z i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun zero i)
    choose t equal using divisible
    refine ⟨t,?_⟩
    ext i
    simpa [Pi.smul_apply,Int.nsmul_eq_mul] using equal i
  · rintro ⟨t,rfl⟩
    ext i
    simp [wrap,Pi.smul_apply,Int.nsmul_eq_mul]

/-- Zero-to-zero reachability in the cover is integer reachability with a multiple displacement. -/
theorem cover_zero_reach_iff (arcs : List (Arc V d)) (M : Nat) (u v : V) :
    CoverReach arcs M (u,0) (v,0) ↔ ∃ t : Lattice d, Reach arcs (u,0) (v,M • t) := by
  constructor
  · intro path
    obtain ⟨z,lifted,zero⟩ := cover_reach_lift arcs M path 0 (wrap_zero M)
    obtain ⟨t,rfl⟩ := (wrap_eq_zero_iff M z).mp zero
    exact ⟨t,lifted⟩
  · rintro ⟨t,path⟩
    have projected := reach_wrap arcs M path
    have zero := (wrap_eq_zero_iff M (M • t)).mpr ⟨t,rfl⟩
    simpa only [wrap_zero,zero] using projected

end LeanTrominoes.PeriodicLatticeGraph
