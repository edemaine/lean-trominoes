/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Source.PeriodicCNFStripSourceFormula
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFPolySpaceProgramSpec
import LeanTrominoes.SAT.CNF.PeriodicCNFTransitionExprNonempty
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFTransitionProgramLiteralCount

/-! # Syntactic facts about the direct PSPACE source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


@[simp] theorem formulaOfSymbols_clauses_length (symbols : List encoding.Γ) :
    (ProgramSource.formulaOfSymbols decider symbols).clauses.length =
      TransitionProgram.clauseCount (ProgramSource.program decider symbols) + 1 := by
  rw [ProgramSource.formula_eq,requireTransitionExpr_clause_length]
  rw [← TransitionExpr.TransitionProgram.clauseCount_program]
  rfl

@[simp] theorem formulaOfSymbols_presentationLiteralCount (symbols : List encoding.Γ) :
    PeriodicCNF.presentationLiteralCount (ProgramSource.formulaOfSymbols decider symbols) =
      TransitionProgram.literalCount (ProgramSource.program decider symbols) + 1 := by
  rw [ProgramSource.formula_eq,requireTransitionExpr_presentationLiteralCount]
  rfl

theorem formulaOfSymbols_widthAtMostThree (symbols : List encoding.Γ) :
    (ProgramSource.formulaOfSymbols decider symbols).WidthAtMost 3 := by
  rw [ProgramSource.formula_eq]
  exact requireTransitionExpr_widthAtMost_three _ _

theorem formulaOfSymbols_clauses_nonempty (symbols : List encoding.Γ) :
    ∀ clause ∈ (ProgramSource.formulaOfSymbols decider symbols).clauses,clause ≠ [] := by
  rw [ProgramSource.formula_eq]
  exact requireTransitionExpr_clauses_nonempty _ _

theorem formulaOfSymbols_sourceAdmissible (symbols : List encoding.Γ) :
    SourceAdmissible (ProgramSource.formulaOfSymbols decider symbols) := by
  have forward : (ProgramSource.formulaOfSymbols decider symbols).IsForwardLocal := by
    rw [ProgramSource.formula_eq]
    exact requireTransitionExpr_forward _ _
  have horizontal := isOneDimensional_of_isForwardLocal forward
  exact ⟨horizontal,(PeriodicCNF.isLocal_iff_isLocalOnLine horizontal).mpr
    (isLocalOnLine_of_isForwardLocal forward),formulaOfSymbols_clauses_nonempty decider symbols⟩

@[simp] theorem sourceFormula_formulaOfSymbols
    (symbols : List encoding.Γ) :
    sourceFormula (ProgramSource.formulaOfSymbols decider symbols) =
      normalizedFormula
        (ProgramSource.formulaOfSymbols decider symbols) := by
  unfold sourceFormula
  rw [if_pos (formulaOfSymbols_sourceAdmissible decider symbols)]

end PeriodicCNFStripReduction
end LeanTrominoes
