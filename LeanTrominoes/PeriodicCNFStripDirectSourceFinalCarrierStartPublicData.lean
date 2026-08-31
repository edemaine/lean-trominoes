/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartRawData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts

/-! # Public/raw direct final-carrier start certificates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierStartPublicDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Opaque certificate exposing the public carrier start as its raw crossover
prefix length. -/
structure DirectSourceFinalCarrierStartRaw
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStart decider symbols =
    directSourceFinalCarrierRawStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
