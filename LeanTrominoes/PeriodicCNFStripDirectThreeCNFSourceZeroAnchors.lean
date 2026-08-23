/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceZeroAnchors
import LeanTrominoes.PeriodicThreeCNFFormulaZeroAnchors

/-! # Zero anchors after direct width-three conversion -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeCNFZeroAnchorStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Width-three conversion preserves the direct transition program's
current-slice clause anchors. -/
theorem directThreeCNFSource_zeroAnchored
    (symbols : List encoding.Γ) :
    (PeriodicThreeCNF.formula
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
        decider symbols)).IsZeroAnchored := by
  exact PeriodicThreeCNF.formula_zeroAnchored _
    (formulaOfSymbols_zeroAnchored decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes
