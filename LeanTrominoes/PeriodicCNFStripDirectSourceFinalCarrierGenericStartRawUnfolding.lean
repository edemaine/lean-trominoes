/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierGenericFamilyStartRawUnfolding
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierGenericStartFamilyUnfolding

/-! # Raw unfolding of the generic direct carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The generic named start unfolds to the shared raw computation. -/
theorem directSourceFinalCarrierGenericStart_raw
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierGenericStartRaw decider symbols := by
  constructor
  exact (directSourceFinalCarrierGenericStart_family decider symbols).eq.trans
    (directSourceFinalCarrierGenericFamilyStart_raw decider symbols).eq

end LeanTrominoes.PeriodicCNFStripReduction

end
