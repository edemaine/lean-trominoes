/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceInput
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkIndex

/-! # Packaged indexed direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkInputStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLinkInputBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  directSourceFinalStructuralBaseDecidableEq

/-- Add a direct tagged link's global carrier index to the packaged source
hypotheses. -/
noncomputable def directSourceFinalCarrierTaggedLinkInput
    (symbols : List encoding.Γ)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat)
    (taggedMember :
      tagged ∈ directSourceFinalCarrierTaggedLinks decider symbols) :
    FinalCarrierTaggedLinkInput
      (directThreeCNFSourceFormula decider symbols)
      tagged.1 tagged.2 where
  sourceInput := directThreeCNFSourceFinalCarrierInput decider symbols
  taggedLinkIndexed :=
    directSourceFinalCarrierTaggedLink_indexed
      decider symbols tagged taggedMember

end LeanTrominoes.PeriodicCNFStripReduction

end
