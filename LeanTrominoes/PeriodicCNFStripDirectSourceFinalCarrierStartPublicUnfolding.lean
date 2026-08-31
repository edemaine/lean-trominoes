/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartPublicData

/-! # Unfolding the public direct final-carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartPublicUnfoldingStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The public start unfolds to the raw crossover-prefix computation. -/
theorem directSourceFinalCarrierStart_raw
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartRaw decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
