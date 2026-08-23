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

/-- All nine-site blocks contributed by the implication-cycle incidence
suffix, before last-occurrence deduplication. -/
def cycleLinkVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (VariableRouteSite (ThreeOccurrenceVariable Variable)) :=
  (cycleLinkIncidences source).flatMap fun incidence =>
    variableRouteSiteBlock incidence.literal.atom incidence.edge.offset

/-- One zero-offset neighboring block for each positional copy in rotated
cycle order. -/
def rotatedVariableRouteSiteBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (VariableRouteSite (ThreeOccurrenceVariable Variable)) :=
  (rotatedOccurrenceVariables source).flatMap fun atom =>
    variableRouteSiteBlock atom (0, 0)

/-- Both incidences of every implication-cycle link have zero normalized
offset, so their site blocks depend only on the endpoint atom. -/
theorem cycleLinkIncidences_variableRouteSiteBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    cycleLinkVariableRouteSites source =
      ((cycleLinkIncidences source).map fun incidence =>
        incidence.literal.atom).flatMap (fun atom =>
          variableRouteSiteBlock atom (0, 0)) := by
  unfold cycleLinkVariableRouteSites cycleLinkIncidences
  rw [List.flatMap_assoc, List.map_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro taggedLink _taggedLinkMember
  rfl

/-- A zero-offset cycle site is present exactly for a genuine positional copy
at one of the nine neighboring translations. -/
@[simp] theorem mem_cycleLinkVariableRouteSites_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable) (position : Cell) :
    (atom, position) ∈ cycleLinkVariableRouteSites source ↔
      atom ∈ allOccurrenceVariables source ∧
        position ∈ neighborTranslations := by
  rw [cycleLinkIncidences_variableRouteSiteBlocks]
  constructor
  · intro siteMember
    rcases List.mem_flatMap.mp siteMember with
      ⟨endpointAtom, endpointMember, blockMember⟩
    rw [variableRouteSiteBlock, List.mem_map] at blockMember
    obtain ⟨translate, translateMember, siteEquality⟩ := blockMember
    have atomEquality := congrArg Prod.fst siteEquality
    have positionEquality := congrArg Prod.snd siteEquality
    have atomEquality' : endpointAtom = atom := by
      simpa using atomEquality
    have positionEquality' : translate = position := by
      simpa [Cell.add] using positionEquality
    subst endpointAtom
    simpa [positionEquality'] using And.intro
      ((mem_cycleLinkIncidenceAtoms_iff source atom).mp endpointMember)
      translateMember
  · rintro ⟨atomMember, positionMember⟩
    have endpointMember :=
      (mem_cycleLinkIncidenceAtoms_iff source atom).mpr atomMember
    apply List.mem_flatMap.mpr
    refine ⟨atom, endpointMember, ?_⟩
    rw [variableRouteSiteBlock, List.mem_map]
    exact ⟨position, positionMember, by simp [Cell.add]⟩

/-- Last-occurrence deduplication of all cycle-link site blocks retains one
nine-site zero-offset block for each copy, in grouped rotated order. -/
theorem cycleLinkVariableRouteSites_dedup_eq_rotatedBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkVariableRouteSites source).dedup =
      rotatedVariableRouteSiteBlocks source := by
  rw [cycleLinkIncidences_variableRouteSiteBlocks]
  rw [List.dedup_flatMap_blocks
    ((cycleLinkIncidences source).map fun incidence =>
      incidence.literal.atom)
    (fun atom => variableRouteSiteBlock atom (0, 0))]
  · rw [cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables]
    rfl
  · exact fun atom => variableRouteSiteBlock_nodup atom (0, 0)
  · intro first second different
    exact variableRouteSiteBlock_disjoint_of_ne different (0, 0) (0, 0)

end PeriodicThreeSATThree
end LeanTrominoes
