/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicThreeSATThreeForwardLocal

/-! # Forward-locality of the direct strip source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceForwardStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem formulaOfSymbols_isForwardLocal
    (symbols : List encoding.Γ) :
    (PolySpaceCompiler.formulaOfSymbols decider symbols).IsForwardLocal := by
  unfold PolySpaceCompiler.formulaOfSymbols
  exact BoundedMachineAtom.designatedMachinePeriodicCNF_forward _ _

/-- Both normalization stages preserve the generated current/next-slice
offset discipline. -/
theorem sourceFormula_isForwardLocal
    (symbols : List encoding.Γ) :
    (sourceFormula
      (PolySpaceCompiler.formulaOfSymbols decider symbols)).IsForwardLocal := by
  rw [sourceFormula_formulaOfSymbols]
  unfold normalizedFormula
  exact PeriodicThreeSATThree.formula_isForwardLocal
    (PeriodicThreeCNF.formula_isForwardLocal
      (formulaOfSymbols_isForwardLocal decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
