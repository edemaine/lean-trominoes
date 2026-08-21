/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPerOccurrenceGroupSizeCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomLastGroupSizeSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankSemantics

/-! # Semantics of per-occurrence source atom-group sizes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomPerOccurrenceGroupSizes

/-- Every emitted field is the full multiplicity of the atom at the same
source occurrence position. -/
theorem sizes_eq_occurrenceAtomCounts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sizes source =
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).map fun atom =>
        (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).count atom := by
  unfold sizes DelimitedBinaryWordTrueCounts.counts
  rw [SourceOccurrenceAtomEqualityRows.rows_eq_semanticRows,
    SourceOccurrenceAtomLastGroupSizes.semanticRows_eq_equalityRows]
  unfold LastRepresentativeEqualityRows.equalityRows
  rw [List.map_map]
  apply List.map_congr_left
  intro atom atomMem
  exact LastRepresentativeEqualityRows.countTrue_equalityRow
    (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula) atom

theorem sizes_getElem?
    (source : SourceSplitRouteDescriptorTokens.Source)
    (index : Nat) :
    (sizes source)[index]? =
      ((SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula)[index]?).map fun atom =>
          (SourceOccurrenceAtomRanks.occurrenceAtoms
            source.formula).count atom := by
  rw [sizes_eq_occurrenceAtomCounts, List.getElem?_map]

theorem sizes_getElem?_eq_some
    (source : SourceSplitRouteDescriptorTokens.Source)
    (index : Nat)
    (indexLt : index <
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).length) :
    (sizes source)[index]? = some
      ((SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).count
        ((SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)[index])) := by
  rw [sizes_getElem?, List.getElem?_eq_getElem indexLt]
  rfl

end SourceOccurrenceAtomPerOccurrenceGroupSizes
end PeriodicCNF
end LeanTrominoes
