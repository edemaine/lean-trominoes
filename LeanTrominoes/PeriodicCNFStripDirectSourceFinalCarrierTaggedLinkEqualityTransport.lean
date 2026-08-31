/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Equality transport for direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkEqualityTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Changing only the propositionally unique base equality leaves the indexed
tagged-link list unchanged. -/
theorem directSourceFinalCarrierTaggedLinks_equalityTransport
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierTaggedLinksEqualityTransport decider symbols := by
  constructor
  unfold directSourceFinalCarrierOriginalTaggedLinks
    directSourceFinalCarrierEqualityAlignedTaggedLinks
  exact congrArg
    (fun equality =>
      directSourceFinalCarrierTaggedLinksFamily decider symbols equality
        (directSourceFinalCarrierStart decider symbols))
    (Subsingleton.elim _ _)

end LeanTrominoes.PeriodicCNFStripReduction

end
