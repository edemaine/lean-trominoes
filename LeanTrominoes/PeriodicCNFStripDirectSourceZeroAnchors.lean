/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFPolySpaceCompiler
import LeanTrominoes.PeriodicCNFRequireTransitionExprZeroAnchors

/-! # Zero anchors of the direct PSPACE source formulas -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Every transition-program clause generated directly from source symbols
starts with a current-slice gate output. -/
theorem formulaOfSymbols_zeroAnchored
    (symbols : List encoding.Γ) :
    (PeriodicCNF.ProgramSource.formulaOfSymbols
      decider symbols).IsZeroAnchored := by
  rw [PeriodicCNF.ProgramSource.formula_eq]
  exact PeriodicCNF.requireTransitionExpr_zeroAnchored _ _

end PeriodicCNFStripReduction
end LeanTrominoes
