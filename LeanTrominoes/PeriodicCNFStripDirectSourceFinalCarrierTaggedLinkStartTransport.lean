/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Start-index transport for direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkStartTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLinkStartTransportBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

local instance directFinalCarrierTaggedLinkStartTransportVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Reindexing by the structural start preserves the complete tagged-link
family. -/
theorem directSourceFinalCarrierTaggedLinks_startTransport
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierTaggedLinksStartTransport decider symbols := by
  constructor
  unfold directSourceFinalCarrierEqualityAlignedTaggedLinks
    directSourceFinalCarrierStructuralTaggedLinks
  exact congrArg
    (directSourceFinalCarrierTaggedLinksFamily decider symbols
      directSourceFinalStructuralBaseDecidableEq)
    (directSourceFinalCarrierStart_structural decider symbols).eq

end LeanTrominoes.PeriodicCNFStripReduction

end
