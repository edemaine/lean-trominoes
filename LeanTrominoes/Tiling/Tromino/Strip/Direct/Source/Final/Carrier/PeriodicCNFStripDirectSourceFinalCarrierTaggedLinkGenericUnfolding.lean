/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTaggedLinkFamilyData

/-! # Generic unfolding of direct-source final carrier links -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicThreeSATThree

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierTaggedLinkGenericUnfoldingBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

local instance directFinalCarrierTaggedLinkGenericUnfoldingVariableDecidableEq :
    DecidableEq Variable :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The structural direct list unfolds to the generic carrier family. -/
theorem directSourceFinalCarrierTaggedLinks_generic
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierTaggedLinksGeneric decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
