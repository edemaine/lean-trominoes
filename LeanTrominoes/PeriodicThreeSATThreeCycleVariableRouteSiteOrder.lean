/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariableRouteSiteBlocks
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceAtomDedup

/-! # Routed-variable site order of the occurrence-cycle suffix -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Both incidences of every implication-cycle link have zero normalized
offset, so their site blocks depend only on the endpoint atom. -/
theorem cycleLinkIncidences_variableRouteSiteBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkIncidences source).flatMap (fun incidence =>
        variableRouteSiteBlock incidence.literal.atom
          incidence.edge.offset) =
      ((cycleLinkIncidences source).map fun incidence =>
        incidence.literal.atom).flatMap (fun atom =>
          variableRouteSiteBlock atom (0, 0)) := by
  unfold cycleLinkIncidences
  rw [List.flatMap_assoc, List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedLink _taggedLinkMember
  rfl

/-- Last-occurrence deduplication of all cycle-link site blocks retains one
nine-site zero-offset block for each copy, in grouped rotated order. -/
theorem cycleLinkVariableRouteSites_dedup_eq_rotatedBlocks
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    ((cycleLinkIncidences source).flatMap fun incidence =>
        variableRouteSiteBlock incidence.literal.atom
          incidence.edge.offset).dedup =
      (rotatedOccurrenceVariables source).flatMap fun atom =>
        variableRouteSiteBlock atom (0, 0) := by
  rw [cycleLinkIncidences_variableRouteSiteBlocks]
  rw [List.dedup_flatMap_blocks
    ((cycleLinkIncidences source).map fun incidence =>
      incidence.literal.atom)
    (fun atom => variableRouteSiteBlock atom (0, 0))]
  · rw [cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables]
  · exact fun atom => variableRouteSiteBlock_nodup atom (0, 0)
  · intro first second different
    exact variableRouteSiteBlock_disjoint_of_ne different (0, 0) (0, 0)

end PeriodicThreeSATThree
end LeanTrominoes
