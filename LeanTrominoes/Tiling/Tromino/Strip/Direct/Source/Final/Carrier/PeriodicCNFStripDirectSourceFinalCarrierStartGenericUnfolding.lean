/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierGenericStartRawUnfolding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStructuralStartRawUnfolding
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierStructuralRawStartEquality

/-! # Generic unfolding of the direct structural carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The direct structural start unfolds to the generic named start. -/
theorem directSourceFinalCarrierStart_generic
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartGeneric decider symbols := by
  constructor
  exact (directSourceFinalCarrierStructuralStart_raw decider symbols).eq.trans
    ((directSourceFinalCarrierStructuralRawStart_equality
      decider symbols).eq.trans
      (directSourceFinalCarrierGenericStart_raw decider symbols).eq.symm)

end LeanTrominoes.PeriodicCNFStripReduction

end
