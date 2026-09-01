/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixCandidateCompiler

/-! # Alignment of sparse variable-incidence suffix candidates -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem routedSparseSuffixTokens_length
    (tokens : List VariableIncidenceDirectionToken) :
    (tokens.flatMap
      VariableIncidenceSparseSuffixToken.routedBlock).length =
        tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [List.flatMap_cons, List.length_append,
        VariableIncidenceSparseSuffixToken.routedBlock_length,
        induction, List.length_cons]
      omega

@[simp] theorem
    directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
      decider symbols).length =
      (directSourceFinalGroupedColoredOccurrenceDirectionTokens
        decider symbols).length +
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateKeys
  rw [List.length_append,
    directSourceFinalGroupedRoutedDirectionTokenKeys_length,
    directSourceFinalGroupedVariableIncidenceKeys_length]

@[simp] theorem
    directSourceFinalGroupedVariableIncidenceSuffixCandidateValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
      decider symbols).length =
      (directSourceFinalGroupedColoredOccurrenceDirectionTokens
        decider symbols).length +
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixCandidateValues
  rw [List.length_append, routedSparseSuffixTokens_length,
    List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
