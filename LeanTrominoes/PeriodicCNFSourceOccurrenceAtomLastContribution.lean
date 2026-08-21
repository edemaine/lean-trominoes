/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPerOccurrenceGroupSizeSemantics
import LeanTrominoes.StableOccurrenceRanksBounds

/-! # Last-occurrence source atom-group contributions -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomLastContributions

/-- Source occurrence ranks paired with their full atom multiplicities. -/
def filterInput (source : SourceSplitRouteDescriptorTokens.Source) :
    UnarySuccessorEqualityFilterMachine.Input where
  ranks := SourceOccurrenceAtomRanks.ranks source
  sizes := SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes source
  valid := by
    rw [SourceOccurrenceAtomRanks.ranks_eq_stableRanks,
      SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes_eq_occurrenceAtomCounts]
    exact StableOccurrenceRanks.ranks_valid
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)

/-- At each source occurrence, retain its atom-group size exactly when that
occurrence is the final presentation of its atom. -/
def contributions (source : SourceSplitRouteDescriptorTokens.Source) :
    List Nat :=
  UnarySuccessorEqualityFilterMachine.selectedValues
    (SourceOccurrenceAtomRanks.ranks source)
    (SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes source)

@[simp] theorem filterInput_ranks
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (filterInput source).ranks = SourceOccurrenceAtomRanks.ranks source := rfl

@[simp] theorem filterInput_sizes
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (filterInput source).sizes =
      SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes source := rfl

@[simp] theorem filterInput_selectedValues
    (source : SourceSplitRouteDescriptorTokens.Source) :
    UnarySuccessorEqualityFilterMachine.selectedValues
        (filterInput source).ranks (filterInput source).sizes =
      contributions source := rfl

end SourceOccurrenceAtomLastContributions
end PeriodicCNF
end LeanTrominoes
