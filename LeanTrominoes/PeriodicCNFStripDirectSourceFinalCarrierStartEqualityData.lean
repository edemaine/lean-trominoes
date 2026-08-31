/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartUnfoldedData

/-! # Equality-implementation certificates for the final carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartEqualityDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Opaque equality between the original and structural crossover-start
computations. -/
structure DirectSourceFinalCarrierStartEqualityIndependent
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierOriginalStart decider symbols =
    directSourceFinalCarrierStructuralStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end

