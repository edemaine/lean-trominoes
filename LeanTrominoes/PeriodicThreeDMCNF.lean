/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicExactOneCNF
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerComputability

/-! # An effective exact-one and CNF presentation of periodic 3DM -/
namespace LeanTrominoes.PeriodicThreeDM.AsCNF
open Gadget Computability NormalizationCompiler

def colors : List WireColor := [.red, .green, .blue]

theorem mem_colors (c : WireColor) : c ∈ colors := by cases c <;> simp [colors]

def literal (i : Incidence) : PeriodicLiteral Nat :=
  ⟨i.tripleIndex, Cell.sub (0,0) i.offset, true⟩

def clause (p : PeriodicThreeDM) (c : WireColor) (v : Nat) : PeriodicClause Nat :=
  (p.incidences c v).map literal

def exactOne (p : PeriodicThreeDM) : PeriodicCNF Nat :=
  ⟨colors.flatMap fun c => (List.range (p.elementCount c)).map (clause p c)⟩

theorem clause_values (p : PeriodicThreeDM) (a : p.MatchingAssignment)
    (c : WireColor) (v : Nat) (x : Cell) :
    PeriodicOneInThree.clauseValues a x (clause p c v) =
      p.incidentValues (p.liftAssignment a) c v x := by
  simp [PeriodicOneInThree.clauseValues, clause, literal, incidentValues,
    liftAssignment, List.map_map, Cell.add, Cell.sub, sub_eq_add_neg]

theorem exactOne_satisfies (p : PeriodicThreeDM) (a : p.MatchingAssignment) :
    PeriodicOneInThree.Satisfies (exactOne p) a ↔ p.Satisfies a := by
  simp only [PeriodicOneInThree.Satisfies, exactOne, List.forall_mem_flatMap,
    List.forall_mem_map, List.mem_range, PeriodicOneInThree.ClauseHolds, clause_values,
    Satisfies, CoversElements]
  constructor
  · intro h c v hv x; exact h x c (mem_colors c) v hv
  · intro h x c _ v hv; exact h c v hv x

def formula (p : PeriodicThreeDM) : PeriodicCNF Nat :=
  PeriodicExactOneCNF.formula (exactOne p)

theorem satisfiable_iff (p : PeriodicThreeDM) : (formula p).Satisfiable ↔ p.Satisfiable := by
  rw [formula, PeriodicExactOneCNF.satisfiable_iff]
  exact exists_congr (exactOne_satisfies p)

private theorem literal_primrec : Primrec literal := by
  have index : Primrec Incidence.tripleIndex := Primrec.fst.comp Incidence.equivData_primrec
  have offset : Primrec Incidence.offset := Primrec.snd.comp Incidence.equivData_primrec
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair index (Primrec.pair
      (cell_sub_primrec.comp (Primrec.const (0,0)) offset) (Primrec.const true)))

private theorem clause_primrec : Primrec fun p : (PeriodicThreeDM × WireColor) × Nat =>
    clause p.1.1 p.1.2 p.2 :=
  Primrec.list_map incidences_primrec (literal_primrec.comp Primrec.snd)

theorem exactOne_primrec : Primrec exactOne := by
  have colorRow : Primrec₂ fun (p : PeriodicThreeDM) (c : WireColor) =>
      (List.range (p.elementCount c)).map (clause p c) :=
    Primrec.list_map (Primrec.list_range.comp elementCount_primrec)
      (clause_primrec.comp (Primrec.pair Primrec.fst Primrec.snd))
  exact PeriodicCNF.equivData_symm_primrec.comp
    (Primrec.list_flatMap (Primrec.const colors) colorRow)

theorem formula_primrec : Primrec formula :=
  PeriodicExactOneCNF.formula_primrec.comp exactOne_primrec

theorem satisfiable_coRE : LeanWang.CoREPred PeriodicThreeDM.Satisfiable := by
  have upper := LeanWang.REPred.comp PeriodicCNF.satisfiable_coRE formula_primrec.to_comp
  exact upper.of_eq fun p => not_congr (satisfiable_iff p)

end LeanTrominoes.PeriodicThreeDM.AsCNF
