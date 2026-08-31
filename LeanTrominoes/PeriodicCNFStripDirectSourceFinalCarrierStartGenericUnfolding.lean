/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierGenericStartRawUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStructuralStartRawUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStructuralRawStartEquality

/-! # Generic unfolding of the direct structural carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartGenericUnfoldingStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct structural start unfolds to the generic named start. -/
theorem directSourceFinalCarrierStart_generic
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartGeneric decider symbols := by
  constructor
  exact (directSourceFinalCarrierStructuralStart_raw decider symbols).eq.trans
    ((directSourceFinalCarrierStructuralRawStart_equality
      decider symbols).eq.trans
      (directSourceFinalCarrierGenericStart_raw decider symbols).eq.symm)

end LeanTrominoes.PeriodicCNFStripReduction

end
