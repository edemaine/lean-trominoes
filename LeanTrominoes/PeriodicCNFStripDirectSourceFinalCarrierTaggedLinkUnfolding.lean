/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Unfolding direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTaggedLinkUnfoldingStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierTaggedLinkUnfoldingBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

local instance directFinalCarrierTaggedLinkUnfoldingVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The public direct list unfolds to the explicit-start generic family. -/
theorem directSourceFinalCarrierTaggedLinks_unfolded
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierTaggedLinksUnfolded decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
