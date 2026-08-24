/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomGroupedMultiplicity
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomStream
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkOccurrenceGroupData

/-! # Multiplicity of cycle-link incidence atoms -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every atom presented by the cycle-link incidence stream occurs exactly
twice in that stream. -/
theorem cycleLinkIncidenceAtoms_count_eq_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ∀ atom ∈ (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom),
      ((cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom)).count atom = 2 := by
  let groups := cycleLinkOccurrenceGroups source
  have atomsEq :
      (cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom) =
        groups.flatMap CycleLinkGroupedPortRanks.cycleLinkAtoms := by
    calc
      (cycleLinkIncidences source).map
          (fun incidence => incidence.literal.atom) =
        CycleLinkGroupedPortRanks.linkAtoms (allCycleLinks source) :=
          CycleLinkGroupedPortRanks.cycleLinkIncidences_atoms source
      _ = CycleLinkGroupedPortRanks.linkAtoms
          (groups.flatMap cycleLinks) := by
            simp [groups, cycleLinkOccurrenceGroups, allCycleLinks,
              List.flatMap_map]
      _ = groups.flatMap CycleLinkGroupedPortRanks.cycleLinkAtoms :=
        CycleLinkGroupedPortRanks.linkAtoms_flatMap_cycleLinks groups
  rw [atomsEq]
  exact CycleLinkGroupedPortRanks.groupedCycleLinkAtoms_count_eq_two
    groups
    (cycleLinkOccurrenceGroups_flatten_nodup source)

end PeriodicThreeSATThree
end LeanTrominoes
