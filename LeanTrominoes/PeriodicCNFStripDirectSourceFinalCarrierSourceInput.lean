/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierSourceFacts
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputData

/-! # Packaged direct-source final-carrier facts -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierSourceInputBaseDecidableEq :
    DecidableEq (ThreeCNFVariable Nat) :=
  Classical.decEq _

/-- Put the lightweight direct width-three facts into the generic source
input expected by final-carrier semantics. -/
noncomputable def directThreeCNFSourceFinalCarrierInput
    (symbols : List encoding.Γ) :
    FinalCarrierSourceInput
      (PeriodicThreeCNF.formula
        (ProgramSource.formulaOfSymbols decider symbols)) where
  sourceFacts := directThreeCNFSourceFinalCarrierFacts decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
