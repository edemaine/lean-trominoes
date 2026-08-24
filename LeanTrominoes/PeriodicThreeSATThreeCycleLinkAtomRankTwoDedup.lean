/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkAtomMultiplicity
import LeanTrominoes.PrefixRankTwoDedupBlocks

/-! # Rank-two selection from cycle atoms -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open CycleLinkGroupedPortRanks

/-- Prefix rank two selects the deduplicated cycle atoms in their
last-occurrence order. -/
theorem cycleLinkIncidenceAtoms_rankTwo_flatMap_eq_dedup
    {Variable Output : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (block : ThreeOccurrenceVariable Variable → List Output) :
    let atoms := (cycleLinkIncidences source).map
      (fun incidence => incidence.literal.atom)
    (atoms.zip (prefixRanks atoms)).flatMap (fun pair =>
        if pair.2 = 2 then block pair.1 else []) =
      atoms.dedup.flatMap block := by
  exact prefixRanks_rankTwo_flatMap_eq_dedup _
    (cycleLinkIncidenceAtoms_count_eq_two source) block

end PeriodicThreeSATThree
end LeanTrominoes
