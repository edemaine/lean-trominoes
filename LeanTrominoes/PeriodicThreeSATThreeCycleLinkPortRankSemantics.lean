/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomStream
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceCountInstances

/-! # Exact target-port ranks of cycle-link incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

/-- The target-port rank field appearing in each explicit cycle-link route
descriptor, in incidence order. -/
def cycleLinkIncidenceTargetPortRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  (cycleLinkIncidences source).zipIdx.map fun tagged =>
    1 + @List.count (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq tagged.1.literal.atom
      (((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).take tagged.2)

theorem cycleLinkIncidenceTargetPortRanks_eq_indexedPrefixRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleLinkIncidenceTargetPortRanks source =
      indexedPrefixRanks
        ((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)) := by
  unfold cycleLinkIncidenceTargetPortRanks indexedPrefixRanks
  rw [List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro tagged _
  dsimp
  rw [occurrenceVariable_count_eq_decidable]

theorem cycleLinkIncidenceTargetPortRanks_eq_prefixRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleLinkIncidenceTargetPortRanks source =
      prefixRanks
        ((cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom)) := by
  rw [cycleLinkIncidenceTargetPortRanks_eq_indexedPrefixRanks,
    ← prefixRanks_eq_indexedPrefixRanks]

/-- Actual descriptor target ranks equal the emitter's two positional rank
fields for every group and every link. -/
theorem cycleLinkIncidenceTargetPortRanks_eq_positional
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleLinkIncidenceTargetPortRanks source =
      (sourceVariables source).flatMap fun atom =>
        positionalRankWord (occurrenceVariables source atom).length := by
  calc
    cycleLinkIncidenceTargetPortRanks source =
        prefixRanks
          ((cycleLinkIncidences source).map
            (fun incidence => incidence.literal.atom)) :=
      cycleLinkIncidenceTargetPortRanks_eq_prefixRanks source
    _ = prefixRanks (linkAtoms (allCycleLinks source)) := by
      rw [cycleLinkIncidences_atoms]
    _ = (sourceVariables source).flatMap fun atom =>
        groupRankWord (occurrenceVariables source atom).length :=
      allCycleLinks_prefixRanks source
    _ = (sourceVariables source).flatMap fun atom =>
        positionalRankWord (occurrenceVariables source atom).length := by
      apply List.flatMap_congr
      intro atom _
      exact (positionalRankWord_eq_groupRankWord _).symm

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
