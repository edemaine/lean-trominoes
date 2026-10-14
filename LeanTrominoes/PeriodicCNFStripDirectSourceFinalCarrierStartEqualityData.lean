/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartOriginalData

/-! # Equality-implementation certificates for the final carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Opaque equality between the original and structural crossover-start
computations. -/
structure DirectSourceFinalCarrierStartEqualityIndependent
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierOriginalStart decider symbols =
    directSourceFinalCarrierStructuralStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
