/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartGenericData

/-! # Family unfolding of the generic direct carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierGenericStartFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The named generic start unfolds to its equality-explicit family. -/
theorem directSourceFinalCarrierGenericStart_family
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierGenericStartFamily decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
