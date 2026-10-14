/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts
import LeanTrominoes.PeriodicThreeSATThreeForwardLocal

/-! # Forward-locality of the direct strip source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


theorem formulaOfSymbols_isForwardLocal
    (symbols : List encoding.Γ) :
    (ProgramSource.formulaOfSymbols decider symbols).IsForwardLocal := by
  rw [ProgramSource.formula_eq]
  exact requireTransitionExpr_forward _ _

/-- Both normalization stages preserve the generated current/next-slice
offset discipline. -/
theorem sourceFormula_isForwardLocal
    (symbols : List encoding.Γ) :
    (sourceFormula
      (ProgramSource.formulaOfSymbols decider symbols)).IsForwardLocal := by
  rw [sourceFormula_formulaOfSymbols]
  unfold normalizedFormula
  exact PeriodicThreeSATThree.formula_isForwardLocal
    (PeriodicThreeCNF.formula_isForwardLocal
      (formulaOfSymbols_isForwardLocal decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
