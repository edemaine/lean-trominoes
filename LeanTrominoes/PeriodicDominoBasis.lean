/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDominoNeighbors
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Executable coordinate decoding for arbitrary nonsingular integer periods

The period vectors are the columns of an integer matrix. Cramer's rule gives
the only possible lattice coordinates for each representative; checking the
reconstructed point handles lattice cosets and holes in the periodic region.
-/
namespace LeanTrominoes.Domino
open PeriodicLatticeGraph
variable {n d : Nat}

structure BasisData (n d : Nat) where
  origin : Fin n → Cell d
  basis : Matrix (Fin d) (Fin d) Int

def BasisData.period (B : BasisData n d) : Lattice d →+ Cell d where
  toFun := B.basis.mulVec
  map_zero' := by simp
  map_add' := Matrix.mulVec_add B.basis

def BasisData.realize (B : BasisData n d) (u : Fin n × Lattice d) : Cell d :=
  B.origin u.1+B.basis.mulVec u.2

def BasisData.Valid (B : BasisData n d) : Prop := B.basis.det≠0 ∧ Function.Injective B.realize

def BasisData.chart (B : BasisData n d) (valid : B.Valid) : Chart (Fin n) d d where
  origin := B.origin
  period := B.period
  injective := valid.2

structure InverseData (d : Nat) where
  numerator : Matrix (Fin d) (Fin d) Int
  denominator : Int

def BasisData.inverseData (B : BasisData n d) : InverseData d := ⟨B.basis.adjugate,B.basis.det⟩

def InverseData.coordinates (I : InverseData d) (x : Cell d) : Lattice d :=
  fun i => (I.numerator.mulVec x) i / I.denominator

theorem BasisData.coordinates_period (B : BasisData n d) (nonzero : B.basis.det≠0) (z : Lattice d) :
    B.inverseData.coordinates (B.basis.mulVec z)=z := by
  funext i
  simp only [InverseData.coordinates,BasisData.inverseData,Matrix.mulVec_mulVec,Matrix.adjugate_mul,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul]
  exact Int.mul_ediv_cancel_left (z i) nonzero

def BasisData.probe (B : BasisData n d) (I : InverseData d) (x : Cell d) (v : Fin n) :
    Option (Fin n × Lattice d) :=
  let z := I.coordinates (x-B.origin v)
  if B.realize (v,z)=x then some (v,z) else none

def firstSome {A B : Type*} (probe : A → Option B) : List A → Option B
  | [] => none
  | v::vs => match probe v with
    | some w => some w
    | none => firstSome probe vs

theorem firstSome_sound {A B : Type*} (probe : A → Option B) (values : List A) (w : B)
    (found : firstSome probe values=some w) : ∃ v∈values, probe v=some w := by
  induction values with
  | nil => simp [firstSome] at found
  | cons v vs ih =>
    cases current : probe v with
    | none =>
      have rest : firstSome probe vs=some w := by simpa [firstSome,current] using found
      obtain ⟨a,ha,equal⟩ := ih rest
      exact ⟨a,List.mem_cons_of_mem _ ha,equal⟩
    | some a =>
      have equal : a=w := by simpa [firstSome,current] using found
      exact ⟨v,List.mem_cons_self,by simpa only [equal] using current⟩

theorem firstSome_none {A B : Type*} (probe : A → Option B) (values : List A)
    (missing : firstSome probe values=none) : ∀ v∈values, probe v=none := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    cases current : probe v with
    | some a => simp [firstSome,current] at missing
    | none =>
      have rest : firstSome probe vs=none := by simpa [firstSome,current] using missing
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact current
      · exact ih rest a ha

def BasisData.decodeWith (B : BasisData n d) (I : InverseData d) (x : Cell d) : Option (Fin n × Lattice d) :=
  firstSome (B.probe I x) (List.finRange n)

theorem BasisData.probe_sound (B : BasisData n d) (I : InverseData d) (x : Cell d)
    (v : Fin n) (u : Fin n × Lattice d) (found : B.probe I x v=some u) : B.realize u=x := by
  unfold BasisData.probe at found
  dsimp only at found
  split_ifs at found with h
  · have equal := Option.some.inj found
    exact equal ▸ h

theorem BasisData.probe_complete (B : BasisData n d) (nonzero : B.basis.det≠0)
    (u : Fin n × Lattice d) : B.probe B.inverseData (B.realize u) u.1=some u := by
  have difference : B.realize u-B.origin u.1=B.basis.mulVec u.2 := by unfold BasisData.realize; abel
  simp only [BasisData.probe,difference,B.coordinates_period nonzero,Prod.mk.eta,ite_true]

theorem BasisData.decode_correct (B : BasisData n d) (valid : B.Valid) (x : Cell d) (u : Fin n × Lattice d) :
    B.decodeWith B.inverseData x=some u ↔ B.realize u=x := by
  constructor
  · intro found
    obtain ⟨v,_,hv⟩ := firstSome_sound (B.probe B.inverseData x) (List.finRange n) u found
    exact B.probe_sound B.inverseData x v u hv
  · intro equal
    cases found : B.decodeWith B.inverseData x with
    | none =>
      have missing := firstSome_none (B.probe B.inverseData x) (List.finRange n) found u.1 (List.mem_finRange _)
      rw [← equal,B.probe_complete valid.1 u] at missing
      contradiction
    | some w =>
      obtain ⟨v,_,hv⟩ := firstSome_sound (B.probe B.inverseData x) (List.finRange n) w found
      have same := valid.2 ((B.probe_sound B.inverseData x v w hv).trans equal.symm)
      exact congrArg some same

def BasisData.graph (B : BasisData n d) (valid : B.Valid) : GraphChart (Fin n) d d :=
  (B.chart valid).graphOfDecoder (B.decodeWith B.inverseData) (B.decode_correct valid)
    (List.finRange n) (fun v => List.mem_finRange v)

theorem BasisData.graph_size (B : BasisData n d) (valid : B.Valid) : (B.graph valid).arcs.length ≤ n*d := by
  simpa only [BasisData.graph,Chart.graphOfDecoder,BasisData.chart,List.length_finRange] using neighborArcs_length B.origin (B.decodeWith B.inverseData) (List.finRange n)

end LeanTrominoes.Domino
