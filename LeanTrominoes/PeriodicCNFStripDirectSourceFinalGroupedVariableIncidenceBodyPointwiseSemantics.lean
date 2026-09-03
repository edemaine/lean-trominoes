/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMapSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionBlockListSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixPointwiseSemantics

/-! # Pointwise complete grouped variable-incidence bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every complete direct variable-incidence body is its finite local prefix
followed by the unique routed suffix at that presentation index, or by the
empty suffix at a non-routed incidence. -/
theorem directSourceFinalGroupedVariableIncidenceBodies_eq_pointwise
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceBodies decider symbols =
      ((directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).zipIdx.map fun tagged =>
          HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
            if tagged.2 ∈
                directSourceFinalGroupedRoutedIncidenceKeys
                  decider symbols then
              FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
                (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
                (directSourceFinalGroupedColoredOccurrenceDirectionBodies
                  decider symbols)
                tagged.2
            else []) := by
  unfold directSourceFinalGroupedVariableIncidenceBodies
    directSourceFinalGroupedVariableIncidencePrefixBodies
  rw [directSourceFinalGroupedVariableIncidenceSuffixBodies_eq_pointwise]
  let queries := directSourceFinalGroupedVariableIncidencePrefixQueries
    decider symbols
  have rangeEq : List.range queries.length =
      queries.zipIdx.map Prod.snd := by
    rw [List.zipIdx_map_snd, List.range_eq_range']
  rw [show directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols = queries by rfl]
  rw [rangeEq, List.map_map, LeanTrominoes.List.zipWith_map_zipIdx]
  simp only [Function.comp_apply]

end LeanTrominoes.PeriodicCNFStripReduction

end
