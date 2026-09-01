/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixData
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Compilers for sparse variable-incidence suffix candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableSuffixCandidateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def
    directSourceFinalGroupedVariableIncidenceSuffixCandidateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
        decider) := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalGroupedRoutedDirectionTokenKeysComputableInPolyTime
      decider)
    (directSourceFinalGroupedVariableIncidenceKeysComputableInPolyTime
      decider)

private noncomputable def
    directSourceFinalGroupedRoutedSparseSuffixTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun symbols : List encoding.Γ =>
        (directSourceFinalGroupedColoredOccurrenceDirectionTokens
          decider symbols).flatMap
            VariableIncidenceSparseSuffixToken.routedBlock) := by
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedColoredOccurrenceDirectionTokensComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      VariableIncidenceSparseSuffixToken.routedBlock)

private noncomputable def
    directSourceFinalGroupedDefaultSparseSuffixTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun symbols : List encoding.Γ =>
        (directSourceFinalGroupedVariableIncidencePrefixQueries
          decider symbols).map fun _ =>
            VariableIncidenceSparseSuffixToken.defaultEnd) := by
  let mapped := FiniteBlockTransducer.computableInPolyTime
    (fun _ : HorizontalFiniteIncidenceDirectionQuery =>
      [VariableIncidenceSparseSuffixToken.defaultEnd])
  simpa only [List.map_eq_flatMap] using
    TM2CompositionMachine.computableInPolyTime
      (directSourceFinalGroupedVariableIncidencePrefixQueriesComputableInPolyTime
        decider)
      mapped

noncomputable def
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValuesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
        decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
    exact TM2ListAppend.computableInPolyTime
      (directSourceFinalGroupedRoutedSparseSuffixTokensComputableInPolyTime
        decider)
      (directSourceFinalGroupedDefaultSparseSuffixTokensComputableInPolyTime
        decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

end LeanTrominoes.PeriodicCNFStripReduction

end
