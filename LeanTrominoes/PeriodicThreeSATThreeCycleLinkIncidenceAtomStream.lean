/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkPrefixRankIndexing
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceData

/-! # Endpoint word of the fixed cycle-link incidence stream -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree
namespace CycleLinkGroupedPortRanks

theorem cycleLinkIncidenceBlock_atoms
    {Variable : Type*}
    (taggedLink :
      (ThreeOccurrenceVariable Variable ×
        ThreeOccurrenceVariable Variable) × Nat) :
    (cycleLinkIncidenceBlock taggedLink).map
        (fun incidence => incidence.literal.atom) =
      [taggedLink.1.1, taggedLink.1.2] := by
  rfl

theorem cycleLinkIncidenceBlocks_atoms
    {Variable : Type*}
    (links : List (ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)) (start : Nat) :
    ((links.zipIdx start).flatMap cycleLinkIncidenceBlock).map
        (fun incidence => incidence.literal.atom) =
      linkAtoms links := by
  induction links generalizing start with
  | nil => rfl
  | cons link links induction =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append,
        cycleLinkIncidenceBlock_atoms, linkAtoms]
      rw [induction]
      rfl

/-- Erasing the fixed incidence metadata leaves the source and target endpoint
of every cycle link, in the original grouped link order. -/
theorem cycleLinkIncidences_atoms
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).map
        (fun incidence => incidence.literal.atom) =
      linkAtoms (allCycleLinks source) := by
  unfold cycleLinkIncidences
  exact cycleLinkIncidenceBlocks_atoms
    (allCycleLinks source) source.clauses.length

end CycleLinkGroupedPortRanks
end PeriodicThreeSATThree
end LeanTrominoes
