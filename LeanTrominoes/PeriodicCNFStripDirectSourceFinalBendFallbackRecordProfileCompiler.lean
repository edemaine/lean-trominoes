/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordProfileFramingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendRouteTailRecordCompiler

/-! # Direct compiler for retained-bend record profiles -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRecordProfileCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalBendFallbackCompiledRecordProfiles
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordProfileFraming.Profile :=
  BinaryRouteTailRecordProfileFraming.recordProfiles
    (directSourceBaseBendRouteTailRecordTokens decider symbols)

noncomputable def
    directSourceFinalBendFallbackCompiledRecordProfilesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackCompiledRecordProfiles decider) := by
  unfold directSourceFinalBendFallbackCompiledRecordProfiles
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceBaseBendRouteTailRecordTokensComputableInPolyTime decider)
    BinaryRouteTailRecordProfileFraming.recordProfilesComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
