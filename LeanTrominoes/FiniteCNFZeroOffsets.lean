/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFWidth
import LeanTrominoes.PeriodicCNFInjectiveRenaming

/-! # Finite formulas as zero-offset periodic presentations -/
namespace LeanTrominoes.FiniteCNF

def erase {V : Type*} (formula : PeriodicCNF V) : Formula V :=
  formula.clauses.map fun clause => clause.map fun literal => (literal.atom,literal.value)

def ZeroOffsets {V : Type*} (formula : PeriodicCNF V) : Prop :=
  ∀ clause∈formula.clauses, ∀ literal∈clause, literal.offset=(0,0)

@[simp] theorem erase_periodize {V : Type*} (formula : Formula V) :
    erase (periodize formula)=formula := by
  simp [erase,periodize,List.map_map,Function.comp_def]

@[simp] theorem periodize_zeroOffsets {V : Type*} (formula : Formula V) :
    ZeroOffsets (periodize formula) := by
  intro clause member literal hl
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨originalLiteral,_,rfl⟩ := List.mem_map.mp hl
  rfl

theorem periodize_erase {V : Type*} (formula : PeriodicCNF V) (zero : ZeroOffsets formula) :
    periodize (erase formula)=formula := by
  cases formula with
  | mk clauses =>
    simp only [periodize,erase,List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id clauses]
    apply List.map_congr_left
    intro clause member
    simp only [Function.comp_def,List.map_map,id_eq]
    conv_rhs => rw [← List.map_id clause]
    apply List.map_congr_left
    intro literal hl
    cases literal with
    | mk atom offset value =>
      simpa using congrArg (fun offset => (⟨atom,offset,value⟩ : PeriodicLiteral V))
        (zero clause member _ hl).symm

theorem satisfiable_erase {V : Type*} (formula : PeriodicCNF V) (zero : ZeroOffsets formula) :
    Satisfiable (erase formula) ↔ formula.Satisfiable := by
  rw [← satisfiable_periodize,periodize_erase formula zero]

@[simp] theorem width_periodize {V : Type*} (formula : Formula V) (width : Nat) :
    (periodize formula).WidthAtMost width ↔ WidthAtMost width formula := by
  simp [PeriodicCNF.WidthAtMost,PeriodicClause.WidthAtMost,WidthAtMost,periodize]

theorem width_erase {V : Type*} (formula : PeriodicCNF V) (width : Nat) :
    WidthAtMost width (erase formula) ↔ formula.WidthAtMost width := by
  simp [PeriodicCNF.WidthAtMost,PeriodicClause.WidthAtMost,WidthAtMost,erase]

theorem zeroOffsets_rename {V W : Type*} (formula : PeriodicCNF V)
    (zero : ZeroOffsets formula) (f : V → W) : ZeroOffsets (formula.rename f) := by
  intro clause member literal hl
  obtain ⟨original,hm,rfl⟩ := List.mem_map.mp member
  obtain ⟨originalLiteral,hlm,rfl⟩ := List.mem_map.mp hl
  exact zero original hm originalLiteral hlm

theorem zeroOffsets_isLocal {V : Type*} (formula : PeriodicCNF V) (zero : ZeroOffsets formula) :
    formula.IsLocal := by
  intro clause member first hf second hs
  simp [PeriodicClause.offsetDistance,zero clause member first hf,zero clause member second hs]

end LeanTrominoes.FiniteCNF
