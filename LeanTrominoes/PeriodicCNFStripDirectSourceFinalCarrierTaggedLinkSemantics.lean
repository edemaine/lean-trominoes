/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkGenericUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkEqualityTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkStartTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkGenericStartTransport

/-! # Generic presentation of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct tagged-link family is the generic final-carrier family of the
direct source formula. -/
theorem directSourceFinalCarrierTaggedLinks_eq_generic
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierTaggedLinks decider symbols =
      @finalCarrierTaggedLinks (ThreeCNFVariable Nat)
        directSourceFinalStructuralBaseDecidableEq
        (directThreeCNFSourceFormula decider symbols) := by
  exact (directSourceFinalCarrierTaggedLinks_unfolded decider symbols).eq.trans
    ((directSourceFinalCarrierTaggedLinks_equalityTransport
      decider symbols).eq.trans
      ((directSourceFinalCarrierTaggedLinks_startTransport
        decider symbols).eq.trans
        ((directSourceFinalCarrierTaggedLinks_genericStartTransport
          decider symbols).eq.trans
          (directSourceFinalCarrierTaggedLinks_generic decider symbols).eq)))

end LeanTrominoes.PeriodicCNFStripReduction

end
