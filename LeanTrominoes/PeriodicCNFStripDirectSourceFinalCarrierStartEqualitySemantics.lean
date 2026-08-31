/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartEqualityData

/-! # Equality independence of the final carrier start -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartEqualitySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierStartEqualitySemanticsBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

/-- Changing only the propositionally unique final-variable equality leaves
the crossover-prefix length unchanged. -/
theorem directSourceFinalCarrierStart_equalityIndependent
    (symbols : List encoding.Γ) :
    DirectSourceFinalCarrierStartEqualityIndependent decider symbols := by
  constructor
  unfold directSourceFinalCarrierOriginalStart
    directSourceFinalCarrierStructuralStart
  exact congrArg (directSourceFinalCarrierStartFamily decider symbols)
    (Subsingleton.elim _ _)

end LeanTrominoes.PeriodicCNFStripReduction

end
