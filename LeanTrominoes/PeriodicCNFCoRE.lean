/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFiniteSearch
import LeanTrominoes.PeriodicOccurrences

/-! # Co-r.e. membership for periodic CNF and its syntactic restrictions -/
namespace LeanTrominoes.PeriodicCNF
open Computability
namespace FiniteSearch

variable {V : Type} [Primcodable V] [DecidableEq V]

theorem mem_primrec {A : Type} [Primcodable A] :
    PrimrecRel fun (a : A) (xs : List A) => a ∈ xs :=
  (Primrec.eq.exists_mem_list.swap).of_eq fun _ _ => by simp

omit [DecidableEq V] in
theorem atoms_primrec : Primrec (@atoms V) :=
  Primrec.list_flatMap Primrec.id (Primrec.list_map Primrec.snd (Primrec.fst.comp Primrec.snd))

theorem check_primrec : PrimrecPred (@Check V _) := by
  have literal : PrimrecRel fun (l : (V × Cell) × Bool) (s : List (V × Cell)) =>
      decide (l.1 ∈ s) = l.2 :=
    Primrec.eq.comp (mem_primrec.decide.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have clause : PrimrecRel fun (c : List ((V × Cell) × Bool)) (s : List (V × Cell)) =>
      ∃ l ∈ c, decide (l.1 ∈ s) = l.2 := literal.exists_mem_list
  have holds : PrimrecRel fun (g : Ground V) (s : List (V × Cell)) =>
      Holds g (fun a => decide (a ∈ s)) := clause.forall_mem_list
  exact holds.swap.exists_mem_list.comp
    (PlaneTilingSearch.subsets_primrec.comp atoms_primrec) Primrec.id

omit [DecidableEq V] in
theorem instantiate_primrec : Primrec₂ (@instantiate V) := by
  have atom : Primrec (fun l : PeriodicLiteral V => l.atom) :=
    Primrec.fst.comp PeriodicLiteral.equivData_primrec
  have offset : Primrec (fun l : PeriodicLiteral V => l.offset) :=
    Primrec.fst.comp (Primrec.snd.comp PeriodicLiteral.equivData_primrec)
  have value : Primrec (fun l : PeriodicLiteral V => l.value) :=
    Primrec.snd.comp (Primrec.snd.comp PeriodicLiteral.equivData_primrec)
  have literal : Primrec₂ fun (c : Cell) (l : PeriodicLiteral V) =>
      ((l.atom, Cell.add c l.offset), l.value) :=
    Primrec.pair (Primrec.pair (atom.comp Primrec.snd)
      (cell_add_primrec.comp Primrec.fst (offset.comp Primrec.snd))) (value.comp Primrec.snd)
  have clause : Primrec₂ fun (c : Cell) (ls : PeriodicClause V) =>
      ls.map (fun l => ((l.atom, Cell.add c l.offset), l.value)) :=
    Primrec.list_map Primrec.snd (literal.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have atCell : Primrec₂ fun (f : PeriodicCNF V) (c : Cell) =>
      f.clauses.map (fun ls => ls.map (fun l => ((l.atom, Cell.add c l.offset), l.value))) :=
    Primrec.list_map (PeriodicCNF.equivData_primrec.comp Primrec.fst)
      (clause.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_flatMap (TrominoAssignment.boxCellList_primrec.comp Primrec.snd)
    (atCell.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

end FiniteSearch

/-- A finite unsatisfiable window witnesses non-satisfiability. -/
theorem satisfiable_coRE {V : Type} [Primcodable V] [DecidableEq V] :
    LeanWang.CoREPred (@Satisfiable V) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun (f : PeriodicCNF V) r => ¬ FiniteSearch.Check (FiniteSearch.instantiate f r))
    (FiniteSearch.check_primrec.comp FiniteSearch.instantiate_primrec).not.computablePred
  exact obstruction.of_eq fun f => by
    rw [FiniteSearch.satisfiable_iff]
    exact not_forall.symm

/-- Any primitive-recursive syntactic restriction can be included as part of
    the decision predicate, with invalid presentations rejected. -/
theorem restricted_coRE {V : Type} [Primcodable V] [DecidableEq V]
    {p : PeriodicCNF V → Prop} (hp : PrimrecPred p) :
    LeanWang.CoREPred (fun f => p f ∧ f.Satisfiable) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun f r => ¬ (p f ∧ FiniteSearch.Check (FiniteSearch.instantiate f r)))
    ((hp.comp Primrec.fst).and
      (FiniteSearch.check_primrec.comp FiniteSearch.instantiate_primrec)).not.computablePred
  exact obstruction.of_eq fun f => by
    rw [← not_forall]
    apply not_congr
    simp only [forall_and, forall_const, ← FiniteSearch.satisfiable_iff]

end LeanTrominoes.PeriodicCNF
