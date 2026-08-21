/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocal

/-! # Forward locality of the named direct source formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceForwardLocalNamedStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directSourceFormula_isForwardLocal
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).IsForwardLocal := by
  unfold directSourceFormula
  exact sourceFormula_isForwardLocal decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes
