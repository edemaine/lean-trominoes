/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteCNFZeroOffsets
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreeOccurrences
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreeCorrectness

/-! # The ordinary finite occurrence-three SAT reduction

The existing implication-cycle construction stays at offset zero on a finite
source. Its semantic correctness and occurrence bound therefore apply to
ordinary finite assignments, without requiring a periodic solution.
-/
namespace LeanTrominoes.FiniteThreeSATThree
open PeriodicThreeSATThree

private theorem cycleFrom_zero {V : Type*} (first current : ThreeOccurrenceVariable V)
    (rest : List (ThreeOccurrenceVariable V)) :
    ∀ clause∈cycleFrom first current rest, ∀ literal∈clause, literal.offset=(0,0) := by
  induction rest generalizing current with
  | nil => simp [cycleFrom,implicationClause]
  | cons next rest ih =>
    intro clause member literal hl
    rcases List.mem_cons.mp member with rfl|member
    · simp only [implicationClause,List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl|rfl <;> rfl
    · exact ih next clause member literal hl

theorem formula_zero {V : Type*} [DecidableEq V] (source : PeriodicCNF V)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (PeriodicThreeSATThree.formula source) := by
  intro clause member literal hl
  rcases List.mem_append.mp member with original|cycle
  · obtain ⟨taggedClause,hm,rfl⟩ := List.mem_map.mp original
    obtain ⟨taggedLiteral,hlm,rfl⟩ := List.mem_map.mp hl
    exact zero taggedClause.1 (List.fst_mem_of_mem_zipIdx hm)
      taggedLiteral.1 (List.fst_mem_of_mem_zipIdx hlm)
  · obtain ⟨atom,_,member⟩ := List.mem_flatMap.mp cycle
    cases h : occurrenceVariables source atom with
    | nil => simp [h,cycleClauses] at member
    | cons first rest =>
      exact cycleFrom_zero first first rest clause (by simpa [h,cycleClauses] using member) literal hl

def formula {V : Type*} [DecidableEq V] (source : FiniteCNF.Formula V) :
    FiniteCNF.Formula (ThreeOccurrenceVariable V) :=
  FiniteCNF.erase (PeriodicThreeSATThree.formula (FiniteCNF.periodize source))

theorem periodize_formula {V : Type*} [DecidableEq V] (source : FiniteCNF.Formula V) :
    FiniteCNF.periodize (formula source)=
      PeriodicThreeSATThree.formula (FiniteCNF.periodize source) :=
  FiniteCNF.periodize_erase _ (formula_zero _ (FiniteCNF.periodize_zeroOffsets source))

theorem satisfiable_iff {V : Type*} [DecidableEq V] (source : FiniteCNF.Formula V) :
    FiniteCNF.Satisfiable (formula source) ↔ FiniteCNF.Satisfiable source := by
  rw [← FiniteCNF.satisfiable_periodize,periodize_formula,
    ← PeriodicThreeSATThree.satisfiable_iff,FiniteCNF.satisfiable_periodize]

theorem width_three {V : Type*} [DecidableEq V] (source : FiniteCNF.Formula V)
    (width : FiniteCNF.WidthAtMost 3 source) : FiniteCNF.WidthAtMost 3 (formula source) := by
  apply (FiniteCNF.width_erase _ _).mpr
  exact formula_widthAtMostThree ((FiniteCNF.width_periodize source 3).mpr width)

theorem occurrences_three {V : Type*} [DecidableEq V] (source : FiniteCNF.Formula V) :
    (FiniteCNF.periodize (formula source)).OccurrencesAtMost 3 := by
  rw [periodize_formula]
  exact formula_occurrencesAtMostThree _

end LeanTrominoes.FiniteThreeSATThree
