/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStartSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Start-index transport for direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
