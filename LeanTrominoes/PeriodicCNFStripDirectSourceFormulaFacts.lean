/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripSourceFormula
import LeanTrominoes.PeriodicCNFPolySpaceProgramSpec
import LeanTrominoes.PeriodicCNFTransitionExprNonempty
import LeanTrominoes.PeriodicCNFTransitionProgramLiteralCount

/-! # Syntactic facts about the direct PSPACE source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceFactsStackFintype
    (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

@[simp] theorem formulaOfSymbols_clauses_length
    (symbols : List encoding.Γ) :
    (PolySpaceCompiler.formulaOfSymbols decider symbols).clauses.length =
      TransitionProgram.clauseCount
          (PolySpaceProgramSpec.program decider symbols) + 1 := by
  unfold PolySpaceCompiler.formulaOfSymbols
    BoundedMachineAtom.designatedMachinePeriodicCNF
  rw [requireTransitionExpr_clause_length]
  rw [← TransitionExpr.TransitionProgram.clauseCount_program]
  simp [PolySpaceProgramSpec.program]

@[simp] theorem formulaOfSymbols_presentationLiteralCount
    (symbols : List encoding.Γ) :
    PeriodicCNF.presentationLiteralCount
        (PolySpaceCompiler.formulaOfSymbols decider symbols) =
      TransitionProgram.literalCount
          (PolySpaceProgramSpec.program decider symbols) + 1 := by
  unfold PolySpaceCompiler.formulaOfSymbols
    BoundedMachineAtom.designatedMachinePeriodicCNF
  rw [requireTransitionExpr_presentationLiteralCount]
  simp [PolySpaceProgramSpec.program]

theorem formulaOfSymbols_widthAtMostThree
    (symbols : List encoding.Γ) :
    (PolySpaceCompiler.formulaOfSymbols decider symbols).WidthAtMost 3 := by
  unfold PolySpaceCompiler.formulaOfSymbols
    BoundedMachineAtom.designatedMachinePeriodicCNF
  exact requireTransitionExpr_widthAtMost_three _ _

theorem formulaOfSymbols_clauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈
        (PolySpaceCompiler.formulaOfSymbols decider symbols).clauses,
      clause ≠ [] := by
  unfold PolySpaceCompiler.formulaOfSymbols
    BoundedMachineAtom.designatedMachinePeriodicCNF
  exact requireTransitionExpr_clauses_nonempty _ _

theorem formulaOfSymbols_sourceAdmissible
    (symbols : List encoding.Γ) :
    SourceAdmissible
      (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  let initial := PolySpaceCompiler.initialConfigurationOfSymbols
    decider symbols
  let accepting := PolySpaceReduction.acceptingConfiguration decider
  have oneDimensional :
      (PolySpaceCompiler.formulaOfSymbols decider symbols).IsOneDimensional := by
    exact BoundedMachineAtom.designatedMachinePeriodicCNF_oneDimensional
      initial accepting
  have localOnLine :
      (PolySpaceCompiler.formulaOfSymbols decider symbols).IsLocalOnLine := by
    exact BoundedMachineAtom.designatedMachinePeriodicCNF_localOnLine
      initial accepting
  exact ⟨oneDimensional,
    (PeriodicCNF.isLocal_iff_isLocalOnLine oneDimensional).mpr localOnLine,
    formulaOfSymbols_clauses_nonempty decider symbols⟩

@[simp] theorem sourceFormula_formulaOfSymbols
    (symbols : List encoding.Γ) :
    sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols) =
      normalizedFormula
        (PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  unfold sourceFormula
  rw [if_pos (formulaOfSymbols_sourceAdmissible decider symbols)]

end PeriodicCNFStripReduction
end LeanTrominoes
