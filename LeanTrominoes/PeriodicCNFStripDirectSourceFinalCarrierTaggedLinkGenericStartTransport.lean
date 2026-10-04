/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartGenericUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Generic-start transport for direct final-carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Reindexing by the generic named start preserves the tagged-link family. -/
theorem directSourceFinalCarrierTaggedLinks_genericStartTransport
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierTaggedLinksGenericStartTransport
      decider symbols := by
  constructor
  unfold directSourceFinalCarrierStructuralTaggedLinks
    directSourceFinalCarrierGenericTaggedLinks
  exact congrArg
    (directSourceFinalCarrierTaggedLinksFamily decider symbols
      directSourceFinalStructuralBaseDecidableEq)
    (directSourceFinalCarrierStart_generic decider symbols).eq

end LeanTrominoes.PeriodicCNFStripReduction

end
