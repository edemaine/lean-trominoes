/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyNodup
import LeanTrominoes.PeriodicCNFStripVariableIncidenceSparseSuffixSelectionSemantics

/-! # Pointwise semantics of direct grouped variable-incidence suffixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The direct sparse suffix table is an ordinary map over all variable
incidence positions: routed positions recover their uniquely aligned body,
and every other position carries the empty suffix. -/
theorem directSourceFinalGroupedVariableIncidenceSuffixBodies_eq_pointwise
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceSuffixBodies decider symbols =
      (List.range
        (directSourceFinalGroupedVariableIncidencePrefixQueries
          decider symbols).length).map fun query =>
        if query ∈
            directSourceFinalGroupedRoutedIncidenceKeys decider symbols then
          FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
            (directSourceFinalGroupedColoredOccurrenceDirectionBodies
              decider symbols)
            query
        else [] := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixBodies
  rw [VariableIncidenceSparseSuffixToken.sparseBodies_eq_map_alignedBody_or_empty
    (aligned := (directSourceFinalGroupedColoredOccurrenceDirectionBodies_length_eq_keys
      decider symbols).symm)
    (keysNodup := directSourceFinalGroupedRoutedIncidenceKeys_nodup
      decider symbols)]
  rw [directSourceFinalGroupedVariableIncidenceKeys_eq_range]

end LeanTrominoes.PeriodicCNFStripReduction

end
