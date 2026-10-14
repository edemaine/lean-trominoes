/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierStartRawData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts

/-! # Public/raw direct final-carrier start certificates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Opaque certificate exposing the public carrier start as its raw crossover
prefix length. -/
structure DirectSourceFinalCarrierStartRaw
    (symbols : List encoding.Γ) : Prop where
  eq : directSourceFinalCarrierStart decider symbols =
    directSourceFinalCarrierRawStart decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
