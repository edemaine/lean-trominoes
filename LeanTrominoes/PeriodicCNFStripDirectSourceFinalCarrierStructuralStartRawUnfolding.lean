/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartGenericData

/-! # Raw unfolding of the direct structural carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStructuralStartRawStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct structural start unfolds to the shared raw computation. -/
theorem directSourceFinalCarrierStructuralStart_raw
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStructuralStartRaw decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
