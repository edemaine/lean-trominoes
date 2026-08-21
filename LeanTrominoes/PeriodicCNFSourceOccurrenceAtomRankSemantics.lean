/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankCompiler
import LeanTrominoes.PeriodicThreeSATThreeOccurrences
import LeanTrominoes.StableOccurrenceRanks

/-! # Semantics of compiled source occurrence ranks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRanks

/-- Source atoms with repetitions, in literal-presentation order. -/
def occurrenceAtoms (formula : PeriodicCNF Nat) : List Nat :=
  (PeriodicThreeSATThree.taggedLiterals formula).map fun tagged =>
    tagged.1.atom

theorem semanticRows_eq_equalityRows (formula : PeriodicCNF Nat) :
    SourceOccurrenceAtomEqualityRows.semanticRows formula =
      (occurrenceAtoms formula).map
        (StableOccurrenceRanks.equalityRow (occurrenceAtoms formula)) := by
  simp [SourceOccurrenceAtomEqualityRows.semanticRows, occurrenceAtoms,
    StableOccurrenceRanks.equalityRow, List.map_map, Function.comp_def]

/-- The compiled rank list is exactly the stable rank of each atom in the
source occurrence stream. -/
theorem ranks_eq_stableRanks
    (source : SourceSplitRouteDescriptorTokens.Source) :
    ranks source =
      StableOccurrenceRanks.ranks (occurrenceAtoms source.formula) := by
  unfold ranks DelimitedBinaryWordPrefixTrueCounts.counts
    StableOccurrenceRanks.ranks
  rw [SourceOccurrenceAtomEqualityRows.rows_words,
    semanticRows_eq_equalityRows]
  exact StableOccurrenceRanks.trueCountsAux_equalityRows
    (occurrenceAtoms source.formula) (occurrenceAtoms source.formula) 0

/-- Indexed form: rank `i` counts equal atoms strictly before occurrence
`i`. -/
theorem ranks_eq_map_zipIdx
    (source : SourceSplitRouteDescriptorTokens.Source) :
    ranks source =
      (occurrenceAtoms source.formula).zipIdx.map fun tagged =>
        ((occurrenceAtoms source.formula).take tagged.2).count tagged.1 := by
  rw [ranks_eq_stableRanks,
    StableOccurrenceRanks.ranks_eq_map_zipIdx]

/-- The atom stream is also the first-coordinate projection of the explicit
occurrence-copy stream. -/
theorem occurrenceAtoms_eq_allOccurrenceVariables_fst
    (formula : PeriodicCNF Nat) :
    occurrenceAtoms formula =
      (PeriodicThreeSATThree.allOccurrenceVariables formula).map Prod.fst := by
  simp [occurrenceAtoms, PeriodicThreeSATThree.allOccurrenceVariables,
    List.map_map, Function.comp_def]

end SourceOccurrenceAtomRanks
end PeriodicCNF
end LeanTrominoes
