/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFDimensionLift

/-! # Theorem 3.2 in every dimension at least two

Both unrestricted and Manhattan-local periodic CNF satisfiability are
co-r.e.-complete under the explicit finite-list encoding. Invalid local
presentations are no-instances. The reduction preserves satisfiability and
locality, rather than adding a promise that formulas use only two coordinates.
-/

namespace LeanTrominoes.PeriodicCNFDimensions
open Computability

theorem planeEmbed_primrec (d : Nat) : Primrec (planeEmbed d) := by
  apply Primrec.fin_curry.mpr
  have coordinate : Primrec (fun a : Cell × Fin d => a.2.val) :=
    (Primrec.dom_finite (fun i : Fin d => i.val)).comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp coordinate (Primrec.const 0))
    (Primrec.fst.comp Primrec.fst)
    (Primrec.ite (Primrec.eq.comp coordinate (Primrec.const 1))
      (Primrec.snd.comp Primrec.fst) (Primrec.const 0))

private theorem natAbs_primrec : Primrec Int.natAbs := by
  apply (Primrec.nat_add.comp int_toNat_primrec
    (int_toNat_primrec.comp int_negate_primrec)).of_eq
  intro z
  cases z <;> simp

theorem distance_primrec (d : Nat) : Primrec₂ (distance d) := by
  induction d with
  | zero => exact Primrec.const 0
  | succ d ih =>
    have tail : Primrec (fun z : Lattice (d + 1) => fun i : Fin d => z i.succ) := by
      apply Primrec.fin_curry.mpr
      exact Primrec.fin_app.comp Primrec.fst
        ((Primrec.dom_finite (fun i : Fin d => i.succ)).comp Primrec.snd)
    have first : Primrec (fun a : Lattice (d + 1) × Lattice (d + 1) =>
        (a.1 0 - a.2 0).natAbs) :=
      natAbs_primrec.comp (int_subtract_primrec.comp
        (Primrec.fin_app.comp Primrec.fst (Primrec.const (0 : Fin (d + 1))))
        (Primrec.fin_app.comp Primrec.snd (Primrec.const (0 : Fin (d + 1)))))
    exact Primrec.nat_add.comp first
      (ih.comp (tail.comp Primrec.fst) (tail.comp Primrec.snd))

theorem isLocal_primrec (d : Nat) : PrimrecPred (IsLocal (d := d)) := by
  have bound : PrimrecRel (fun (first second : PeriodicConstraints.Literal (Lattice d)) =>
      distance d first.1.2 second.1.2 ≤ 1) :=
    Primrec.nat_le.comp (distance_primrec d |>.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) (Primrec.const 1)
  have clause : PrimrecPred (fun clause : List (PeriodicConstraints.Literal (Lattice d)) =>
      ∀ first ∈ clause, ∀ second ∈ clause,
        distance d first.1.2 second.1.2 ≤ 1) :=
    bound.swap.forall_mem_list.swap.forall_mem_list.comp Primrec.id Primrec.id
  exact clause.forall_mem_list

theorem liftLiteral_primrec {V : Type} [Primcodable V] (d : Nat) :
    Primrec (liftLiteral (V := V) d) :=
  Primrec.pair
    (Primrec.pair (Primrec.encode.comp (Primrec.fst.comp PeriodicLiteral.equivData_primrec))
      (planeEmbed_primrec d |>.comp
        (Primrec.fst.comp (Primrec.snd.comp PeriodicLiteral.equivData_primrec))))
    (Primrec.snd.comp (Primrec.snd.comp PeriodicLiteral.equivData_primrec))

theorem liftPlane_primrec {V : Type} [Primcodable V] (d : Nat) :
    Primrec (liftPlane (V := V) d) :=
  Primrec.list_map PeriodicCNF.equivData_primrec
    (Primrec.list_map Primrec.snd ((liftLiteral_primrec d).comp Primrec.snd))

def LocalProblem {d : Nat} (f : Formula d) : Prop :=
  IsLocal f ∧ PeriodicConstraints.Satisfiable (Lattice d) f

theorem satisfiable_coRE (d : Nat) :
    LeanWang.CoREPred (PeriodicConstraints.Satisfiable (Lattice d)) :=
  PeriodicConstraints.satisfiable_coRE (PeriodicSubspaceTiling.lattice_add_primrec d)

theorem localProblem_coRE (d : Nat) : LeanWang.CoREPred (LocalProblem (d := d)) := by
  let restricted : Formula d → Formula d := fun f => if IsLocal f then f else [[]]
  have compiler : Primrec restricted :=
    Primrec.ite (isLocal_primrec d) Primrec.id (Primrec.const [[]])
  have correct (f : Formula d) :
      PeriodicConstraints.Satisfiable (Lattice d) (restricted f) ↔ LocalProblem f := by
    by_cases locality : IsLocal f
    · simp [restricted, locality, LocalProblem]
    · simp [restricted, locality, LocalProblem, PeriodicConstraints.Satisfiable,
        PeriodicConstraints.Holds]
  exact (LeanWang.REPred.comp (satisfiable_coRE d) compiler.to_comp).of_eq
    (fun f => not_congr (correct f))

theorem satisfiable_coREHard {d : Nat} (dimension : 2 ≤ d) :
    LeanWang.CoREHard (PeriodicConstraints.Satisfiable (Lattice d)) := by
  intro A _ source hs
  obtain ⟨reduce, computable, correct⟩ := WangPeriodicCNF.coREHard source hs
  refine ⟨liftPlane d ∘ reduce, (liftPlane_primrec d).to_comp.comp computable, ?_⟩
  intro a
  exact (correct a).trans (liftPlane_satisfiable_iff dimension (reduce a)).symm

theorem localProblem_coREHard {d : Nat} (dimension : 2 ≤ d) :
    LeanWang.CoREHard (LocalProblem (d := d)) := by
  intro A _ source hs
  obtain ⟨reduce, computable, correct⟩ := WangPeriodicCNF.localCoREHard source hs
  refine ⟨liftPlane d ∘ reduce, (liftPlane_primrec d).to_comp.comp computable, ?_⟩
  intro a
  apply (correct a).trans
  change (reduce a).IsLocal ∧ (reduce a).Satisfiable ↔ LocalProblem (liftPlane d (reduce a))
  simp [LocalProblem, liftPlane_local_iff dimension, liftPlane_satisfiable_iff dimension]

/-- The unrestricted higher-dimensional clause of Theorem 3.2. -/
theorem satisfiable_coREComplete {d : Nat} (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (PeriodicConstraints.Satisfiable (Lattice d)) :=
  ⟨satisfiable_coRE d, satisfiable_coREHard dimension⟩

/-- The local higher-dimensional clause of Theorem 3.2. -/
theorem localProblem_coREComplete {d : Nat} (dimension : 2 ≤ d) :
    LeanWang.CoREComplete (LocalProblem (d := d)) :=
  ⟨localProblem_coRE d, localProblem_coREHard dimension⟩

end LeanTrominoes.PeriodicCNFDimensions
