/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceTilingCoRE

/-! # General periodic tiling completion by mandatory placement orbits

A prescribed placement orbit is a tile kind anchored at its fundamental-domain
representative. All of its translates must occur. The chosen completion may
be nonperiodic. Containment and overlap are checked by the tiling constraints.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling
open Computability
variable {G : Type} [AddCommGroup G] [DecidableEq G]

abbrev CompletionInput (G : Type) := Input G × List Nat

def IsCompletion (input : CompletionInput G) (selected : Nat → G → Bool) : Prop :=
  IsTiling input.1 selected ∧ ∀ k ∈ input.2, ∀ z, selected k z=true

def Completable (input : CompletionInput G) : Prop := ∃ selected, IsCompletion input selected

def completionFormula (input : CompletionInput G) : PeriodicConstraints.Formula G :=
  formula input.1 ++ input.2.map (fun k => [((k,0),true)])

theorem completionFormula_holds (input : CompletionInput G) (a : Nat → G → Bool) :
    PeriodicConstraints.Holds G (completionFormula input) a ↔ IsCompletion input a := by
  unfold completionFormula PeriodicConstraints.Holds IsCompletion
  simp only [List.forall_mem_append,forall_and,List.forall_mem_map,List.mem_singleton,
    exists_eq_left,add_zero]
  change (PeriodicConstraints.Holds G (formula input.1) a ∧ _) ↔ _
  rw [formula_holds]
  constructor
  · rintro ⟨tiled,forced⟩; exact ⟨tiled,fun k hk z => forced z k hk⟩
  · rintro ⟨tiled,forced⟩; exact ⟨tiled,fun z k hk => forced k hk z⟩

theorem completable_iff_formula (input : CompletionInput G) :
    Completable input ↔ PeriodicConstraints.Satisfiable G (completionFormula input) :=
  exists_congr fun a => (completionFormula_holds input a).symm

variable [Primcodable G]
theorem completionFormula_primrec (neg_pr : Primrec (fun z : G => -z)) :
    Primrec (@completionFormula G _ _) := by
  have unit : Primrec₂ fun (_input : CompletionInput G) (k : Nat) => [((k,(0 : G)),true)] :=
    Primrec.list_cons.comp
      (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const (0 : G))) (Primrec.const true))
      (Primrec.const [])
  exact Primrec.list_append.comp ((formula_primrec neg_pr).comp Primrec.fst)
    (Primrec.list_map Primrec.snd unit)

/-- The completion half of the general co-r.e. membership statement. -/
theorem completable_coRE (add_pr : Primrec₂ (fun x y : G => x+y))
    (neg_pr : Primrec (fun z : G => -z)) : LeanWang.CoREPred (@Completable G _) := by
  have constraints := PeriodicConstraints.satisfiable_coRE add_pr
  have preimage := LeanWang.REPred.comp constraints (completionFormula_primrec neg_pr).to_comp
  exact preimage.of_eq fun input => not_congr (completable_iff_formula input).symm

theorem lattice_completable_coRE (d : Nat) :
    LeanWang.CoREPred (@Completable (Fin d → Int) _) :=
  completable_coRE (lattice_add_primrec d) (lattice_neg_primrec d)

end LeanTrominoes.PeriodicSubspaceTiling
