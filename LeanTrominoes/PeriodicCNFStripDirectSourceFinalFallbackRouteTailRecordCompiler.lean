/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterCompiler
import LeanTrominoes.BinaryRouteTailRecordProfileFramingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteDirectionCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compilers for carrier and bend fallback route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

def directSourceFinalCarrierFallbackCompiledRecordProfiles
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordProfileFraming.Profile :=
  BinaryRouteTailRecordProfileFraming.recordProfiles
    (directSourceCarrierRouteTailRecordTokens decider symbols)

def directSourceFinalBendFallbackCompiledRecordProfiles
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordProfileFraming.Profile :=
  BinaryRouteTailRecordProfileFraming.recordProfiles
    (directSourceBaseBendRouteTailRecordTokens decider symbols)

/-- Profile framing of the existing carrier headers with the complete final
fallback route words. -/
def directSourceFinalCarrierFallbackCompiledRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordProfileFraming.framed
    (directSourceFinalCarrierFallbackCompiledRecordProfiles decider symbols)
    (directSourceFinalCarrierFallbackRouteDirections decider symbols)

/-- Profile framing of the existing bend headers with the complete final
fallback route words. -/
def directSourceFinalBendFallbackCompiledRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordProfileFraming.framed
    (directSourceFinalBendFallbackCompiledRecordProfiles decider symbols)
    (directSourceFinalBendFallbackRouteDirections decider symbols)

def directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.output
    (directSourceFinalCarrierFallbackCompiledRecordInputTokens
      decider symbols)

def directSourceFinalBendFallbackCompiledRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.output
    (directSourceFinalBendFallbackCompiledRecordInputTokens
      decider symbols)

noncomputable def
    directSourceFinalCarrierFallbackCompiledRecordProfilesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackCompiledRecordProfiles decider) := by
  unfold directSourceFinalCarrierFallbackCompiledRecordProfiles
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceCarrierRouteTailRecordTokensComputableInPolyTime decider)
    BinaryRouteTailRecordProfileFraming.recordProfilesComputableInPolyTime

noncomputable def
    directSourceFinalBendFallbackCompiledRecordProfilesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackCompiledRecordProfiles decider) := by
  unfold directSourceFinalBendFallbackCompiledRecordProfiles
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceBaseBendRouteTailRecordTokensComputableInPolyTime decider)
    BinaryRouteTailRecordProfileFraming.recordProfilesComputableInPolyTime

noncomputable def
    directSourceFinalCarrierFallbackCompiledRecordInputTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackCompiledRecordInputTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCarrierFallbackCompiledRecordInputTokens
    exact BinaryRouteTailRecordProfileFraming.framedComputableInPolyTimeOf
      id
      (directSourceFinalCarrierFallbackCompiledRecordProfiles decider)
      (directSourceFinalCarrierFallbackRouteDirections decider)
      (directSourceFinalCarrierFallbackCompiledRecordProfilesComputableInPolyTime
        decider)
      (directSourceFinalCarrierFallbackRouteDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

noncomputable def
    directSourceFinalBendFallbackCompiledRecordInputTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackCompiledRecordInputTokens decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalBendFallbackCompiledRecordInputTokens
    exact BinaryRouteTailRecordProfileFraming.framedComputableInPolyTimeOf
      id
      (directSourceFinalBendFallbackCompiledRecordProfiles decider)
      (directSourceFinalBendFallbackRouteDirections decider)
      (directSourceFinalBendFallbackCompiledRecordProfilesComputableInPolyTime
        decider)
      (directSourceFinalBendFallbackRouteDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

noncomputable def
    directSourceFinalCarrierFallbackCompiledRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens
        decider) := by
  unfold directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCarrierFallbackCompiledRecordInputTokensComputableInPolyTime
      decider)
    BinaryRouteTailRecordBatchFormatter.outputComputableInPolyTime

noncomputable def
    directSourceFinalBendFallbackCompiledRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendFallbackCompiledRouteTailRecordTokens decider) := by
  unfold directSourceFinalBendFallbackCompiledRouteTailRecordTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalBendFallbackCompiledRecordInputTokensComputableInPolyTime
      decider)
    BinaryRouteTailRecordBatchFormatter.outputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
