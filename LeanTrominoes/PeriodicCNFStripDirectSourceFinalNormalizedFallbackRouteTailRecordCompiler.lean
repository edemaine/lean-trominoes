/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterCompiler
import LeanTrominoes.BinaryRouteTailRecordProfileFramingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteTailRecordCompiler
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Direct compilers for normalized carrier and bend fallback records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalNormalizedFallbackRecordCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Profile framing of the established carrier headers with canonical
normalized complete fallback routes. -/
def directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordProfileFraming.framed
    (directSourceFinalCarrierFallbackCompiledRecordProfiles decider symbols)
    (directSourceFinalCarrierNormalizedFallbackRouteDirections decider symbols)

/-- Profile framing of the established bend headers with canonical normalized
complete fallback routes. -/
def directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
    (symbols : List encoding.Γ) :
    List BinaryRouteTailRecordBatchFormatter.Token :=
  BinaryRouteTailRecordProfileFraming.framed
    (directSourceFinalBendFallbackCompiledRecordProfiles decider symbols)
    (directSourceFinalBendNormalizedFallbackRouteDirections decider symbols)

def directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.output
    (directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
      decider symbols)

def directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  BinaryRouteTailRecordBatchFormatter.output
    (directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
      decider symbols)

noncomputable def
    directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
        decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
    exact BinaryRouteTailRecordProfileFraming.framedComputableInPolyTimeOf
      id
      (directSourceFinalCarrierFallbackCompiledRecordProfiles decider)
      (directSourceFinalCarrierNormalizedFallbackRouteDirections decider)
      (directSourceFinalCarrierFallbackCompiledRecordProfilesComputableInPolyTime
        decider)
      (directSourceFinalCarrierNormalizedFallbackRouteDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

noncomputable def
    directSourceFinalBendNormalizedFallbackCompiledRecordInputTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
        decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
    exact BinaryRouteTailRecordProfileFraming.framedComputableInPolyTimeOf
      id
      (directSourceFinalBendFallbackCompiledRecordProfiles decider)
      (directSourceFinalBendNormalizedFallbackRouteDirections decider)
      (directSourceFinalBendFallbackCompiledRecordProfilesComputableInPolyTime
        decider)
      (directSourceFinalBendNormalizedFallbackRouteDirectionsComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

noncomputable def
    directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
        decider) := by
  unfold directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokensComputableInPolyTime
      decider)
    BinaryRouteTailRecordBatchFormatter.outputComputableInPolyTime

noncomputable def
    directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
        decider) := by
  unfold directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalBendNormalizedFallbackCompiledRecordInputTokensComputableInPolyTime
      decider)
    BinaryRouteTailRecordBatchFormatter.outputComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
