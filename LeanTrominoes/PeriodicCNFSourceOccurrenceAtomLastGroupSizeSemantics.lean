/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowCountsSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowSemantics

/-! # Last-occurrence-ordered source atom-group sizes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomLastGroupSizes

def occurrenceAtoms (formula : PeriodicCNF Nat) : List Nat :=
  (PeriodicThreeSATThree.taggedLiterals formula).map fun tagged =>
    tagged.1.atom

def rows (source : SourceSplitRouteDescriptorTokens.Source) :
    DelimitedBinaryWords.Input :=
  LastRepresentativeEqualityRows.rows
    (SourceOccurrenceAtomEqualityRows.rows source)

def sizes (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts (rows source)

theorem semanticRows_eq_equalityRows (formula : PeriodicCNF Nat) :
    SourceOccurrenceAtomEqualityRows.semanticRows formula =
      LastRepresentativeEqualityRows.equalityRows
        (occurrenceAtoms formula) := by
  simp [SourceOccurrenceAtomEqualityRows.semanticRows,
    LastRepresentativeEqualityRows.equalityRows,
    LastRepresentativeEqualityRows.equalityRow, occurrenceAtoms,
    List.map_map, Function.comp_def]

theorem sourceVariables_eq_dedup_occurrenceAtoms
    (formula : PeriodicCNF Nat) :
    PeriodicThreeSATThree.sourceVariables formula =
      (occurrenceAtoms formula).dedup := by
  rfl

/-- The corrected size stream agrees exactly with the variable-block order
used by the occurrence-splitting reduction. -/
theorem sizes_eq_sourceVariableCounts
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sizes source =
      (PeriodicThreeSATThree.sourceVariables source.formula).map fun atom =>
        (occurrenceAtoms source.formula).count atom := by
  unfold sizes rows
  rw [SourceOccurrenceAtomEqualityRows.rows_eq_semanticRows,
    semanticRows_eq_equalityRows,
    LastRepresentativeEqualityRows.trueCounts_rows_equalityRows,
    sourceVariables_eq_dedup_occurrenceAtoms]

end SourceOccurrenceAtomLastGroupSizes
end PeriodicCNF
end LeanTrominoes
