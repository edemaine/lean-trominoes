/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteTailRecordCompiler

/-! # Direct compiler for retained-carrier record profiles -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRecordProfileCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalCarrierFallbackCompiledRecordProfiles
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordProfileFraming.Profile :=
  BinaryRouteTailRecordProfileFraming.recordProfiles
    (directSourceCarrierRouteTailRecordTokens decider symbols)

noncomputable def
    directSourceFinalCarrierFallbackCompiledRecordProfilesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackCompiledRecordProfiles decider) := by
  unfold directSourceFinalCarrierFallbackCompiledRecordProfiles
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierRouteTailRecordTokensComputableInPolyTime decider)
    BinaryRouteTailRecordProfileFraming.recordProfilesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
