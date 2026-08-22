/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastOccurrenceBlockStarts
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPerOccurrenceBlockStartCompiler

/-! # Semantics of source atom-block starts in occurrence order -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomPerOccurrenceBlockStarts

/-- The compiled lookup stream is exactly the stable source occurrence list
with every atom's last-occurrence-ordered block start broadcast to it. -/
theorem starts_eq_lastOccurrenceBlockStarts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    starts source =
      LastOccurrenceBlockStarts.starts
        (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula) := by
  unfold starts lookupInput
  change LastTrueUnaryValueLookupMachine.lookups
      (SourceOccurrenceAtomEqualityRows.rows source).words
      (SourceOccurrenceAtomContributionStarts.starts source) = _
  rw [SourceOccurrenceAtomEqualityRows.rows_words,
    SourceOccurrenceAtomRanks.semanticRows_eq_equalityRows,
    SourceOccurrenceAtomContributionStarts.starts,
    SourceOccurrenceAtomLastContributions.contributions_eq_lastOccurrenceContributions]
  exact LastOccurrenceBlockStarts.lookups_equalityRows_contributionStarts
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)

@[simp] theorem starts_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (starts source).length =
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).length := by
  rw [starts_eq_lastOccurrenceBlockStarts]
  simp [LastOccurrenceBlockStarts.starts]

/-- Optional lookup at a source occurrence maps its atom to that atom's
dedup-last-ordered block start. -/
theorem starts_getElem?
    (source : SourceSplitRouteDescriptorTokens.Source) (index : Nat) :
    (starts source)[index]? =
      ((SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula)[index]?).map
        (LastOccurrenceBlockStarts.blockStart
          (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)) := by
  rw [starts_eq_lastOccurrenceBlockStarts]
  simp [LastOccurrenceBlockStarts.starts, List.getElem?_map]

end SourceOccurrenceAtomPerOccurrenceBlockStarts
end PeriodicCNF
end LeanTrominoes
