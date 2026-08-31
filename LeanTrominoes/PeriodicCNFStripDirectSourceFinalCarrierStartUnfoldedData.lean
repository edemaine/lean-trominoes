/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartFamilyData

/-! # Unfolded final-carrier start certificates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartUnfoldedDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The original crossover-prefix computation hidden behind a small name. -/
def directSourceFinalCarrierOriginalStart
    (symbols : List encoding.Γ) : Nat :=
  directSourceFinalCarrierStartFamily decider symbols
    directSourceVariableDecidableEq

/-- Opaque certificate exposing the public start with its original equality
implementation. -/
structure DirectSourceFinalCarrierStartUnfolded
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStart decider symbols =
    directSourceFinalCarrierOriginalStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
