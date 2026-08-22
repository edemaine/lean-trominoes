/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPerOccurrenceGroupSizeSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRotatedRankCompiler
import LeanTrominoes.UnaryRotatedRanksSemantics

/-! # Semantics of compiled source occurrence rotated ranks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomRotatedRanks

private theorem zipWith_rankAndSizeMaps
    (all remaining : List Nat) (start : Nat) :
    List.zipWith UnaryRotatedRanksMachine.rotatedRank
        ((remaining.zipIdx start).map fun tagged =>
          (all.take tagged.2).count tagged.1)
        (remaining.map fun atom => all.count atom) =
      (remaining.zipIdx start).map fun tagged =>
        UnaryRotatedRanksMachine.rotatedRank
          ((all.take tagged.2).count tagged.1) (all.count tagged.1) := by
  induction remaining generalizing start with
  | nil => rfl
  | cons atom remaining induction =>
      simp only [List.zipIdx_cons, List.map_cons,
        List.zipWith_cons_cons]
      rw [induction]

/-- The compiler rotates each source occurrence's stable rank within the
complete block of equal atoms. -/
theorem ranks_eq_map_zipIdx
    (source : SourceSplitRouteDescriptorTokens.Source) :
    ranks source =
      (SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula).zipIdx.map fun tagged =>
          UnaryRotatedRanksMachine.rotatedRank
            (((SourceOccurrenceAtomRanks.occurrenceAtoms
              source.formula).take tagged.2).count tagged.1)
            ((SourceOccurrenceAtomRanks.occurrenceAtoms
              source.formula).count tagged.1) := by
  unfold ranks
  rw [UnaryRotatedRanksMachine.rotatedRanks_eq_zipWith
      (rotationInput source).valid,
    rotationInput_ranks, rotationInput_sizes,
    SourceOccurrenceAtomRanks.ranks_eq_map_zipIdx,
    SourceOccurrenceAtomPerOccurrenceGroupSizes.sizes_eq_occurrenceAtomCounts]
  exact zipWith_rankAndSizeMaps
    (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula)
    (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula) 0

@[simp] theorem ranks_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (ranks source).length =
      (SourceOccurrenceAtomRanks.occurrenceAtoms source.formula).length := by
  rw [ranks_eq_map_zipIdx]
  simp

/-- Optional lookup form of the rotated-rank characterization. -/
theorem ranks_getElem?
    (source : SourceSplitRouteDescriptorTokens.Source) (index : Nat) :
    (ranks source)[index]? =
      ((SourceOccurrenceAtomRanks.occurrenceAtoms
        source.formula)[index]?).map fun atom =>
          UnaryRotatedRanksMachine.rotatedRank
            (((SourceOccurrenceAtomRanks.occurrenceAtoms
              source.formula).take index).count atom)
            ((SourceOccurrenceAtomRanks.occurrenceAtoms
              source.formula).count atom) := by
  rw [ranks_eq_map_zipIdx, List.getElem?_map, List.getElem?_zipIdx]
  simp [Function.comp_def]

end SourceOccurrenceAtomRotatedRanks
end PeriodicCNF
end LeanTrominoes
