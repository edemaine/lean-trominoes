/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteCNFZeroOffsets
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization

/-! # Finite semantics when each periodic clause has a common offset -/
namespace LeanTrominoes.FiniteCNF

def UniformOffsets {V : Type*} (formula : PeriodicCNF V) : Prop :=
  ∀ clause∈formula.clauses, ∃ offset, ∀ literal∈clause, literal.offset=offset

theorem uniformOffsets_anchorNormalize {V : Type*} (formula : PeriodicCNF V)
    (uniform : UniformOffsets formula) : ZeroOffsets formula.anchorNormalize := by
  intro clause member literal hl
  obtain ⟨original,originalMember,clauseEq⟩ := List.mem_map.mp member
  subst clause
  obtain ⟨offset,all⟩ := uniform original originalMember
  obtain ⟨oldLiteral,oldMember,literalEq⟩ := List.mem_map.mp hl
  subst literal
  have anchor : PeriodicCNF.clauseAnchor original=offset := by
    cases original with
    | nil => simp at oldMember
    | cons first rest => exact all first (by simp)
  simp [PeriodicLiteral.anchorNormalize,all oldLiteral oldMember,anchor,Cell.sub]

@[simp] theorem erase_anchorNormalize {V : Type*} (formula : PeriodicCNF V) :
    erase formula.anchorNormalize=erase formula := by
  simp [erase,PeriodicCNF.anchorNormalize,PeriodicClause.anchorNormalize,
    PeriodicLiteral.anchorNormalize,List.map_map,Function.comp_def]

theorem satisfiable_erase_of_uniform {V : Type*} (formula : PeriodicCNF V)
    (uniform : UniformOffsets formula) : Satisfiable (erase formula) ↔ formula.Satisfiable := by
  rw [← erase_anchorNormalize formula,satisfiable_erase _ (uniformOffsets_anchorNormalize formula uniform),
    PeriodicCNF.anchorNormalize_satisfiable_iff]

end LeanTrominoes.FiniteCNF
