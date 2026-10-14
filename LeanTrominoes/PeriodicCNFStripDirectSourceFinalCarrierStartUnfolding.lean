/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartUnfoldedData

/-! # Unfolding the raw direct-source final carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The raw start unfolds to its original equality-parameterized computation. -/
theorem directSourceFinalCarrierStart_unfolded
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartUnfolded decider symbols := by
  constructor
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
