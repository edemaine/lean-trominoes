/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMPrivateIncidences

/-!
# Fixed-red private incidences in the planar periodic 3DM assembly

This file localizes every private colored element of the seven-triple
fixed-red detour to its unique occurrence block.  The resulting global
incidence lists are exactly the local Figure 6 neighbor lists, so all eight
private elements retain degree two after assembly.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

def fixedRedPhysicalRed :
    FixedRedInternalRed → FixedRedConnectorRed
  | .middleRung => .middleRung
  | .topAuxiliary => .topAuxiliary

def fixedRedPhysicalGreen :
    FixedRedInternalGreen → FixedRedConnectorGreen
  | .leftRung => .leftRung
  | .topRightLink => .topRightLink
  | .bottomRightLink => .bottomRightLink

def fixedRedPhysicalBlue :
    FixedRedInternalBlue → FixedRedConnectorBlue
  | .topLeftLink => .topLeftLink
  | .bottomLeftLink => .bottomLeftLink
  | .rightRung => .rightRung

theorem occurrenceBlock_redFixedRed_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable × OccurrenceSlot)
    (kindEq :
      occurrenceConnectorKind source target.1 target.2 = .fixedRed)
    (element : FixedRedInternalRed) :
    (occurrenceTriples source current.1 current.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom =
              RedElement.fixedRedInternal target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        ((fixedRedPhysicalRed element).neighbors).map fun triple =>
          ⟨.fixedRed target.1 target.2 triple, (0, 0)⟩
      else
        [] := by
  rcases current with ⟨currentAtom, currentSlot⟩
  rcases target with ⟨targetAtom, targetSlot⟩
  by_cases sameAtom : currentAtom = targetAtom
  · subst currentAtom
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases element <;>
        simp_all [occurrenceTriples, allFixedRedTriples,
          tripleReferences, fixedRedTripleReferences,
          FixedRedConnectorTriple.references,
          fixedRedRedElement, fixedRedPhysicalRed,
          FixedRedConnectorRed.neighbors, redClauseTerminal]
    · cases currentKind :
          occurrenceConnectorKind source targetAtom currentSlot <;>
        cases element <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryRedElement, fixedRedRedElement,
          redClauseTerminal]
  · cases currentKind :
        occurrenceConnectorKind source currentAtom currentSlot <;>
      cases element <;>
      simp_all [occurrenceTriples, allOrdinaryTriples,
        allFixedRedTriples, tripleReferences,
        ordinaryTripleReferences, fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryRedElement, fixedRedRedElement,
        redClauseTerminal]

set_option maxHeartbeats 800000 in
theorem occurrenceBlock_greenFixedRed_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable × OccurrenceSlot)
    (kindEq :
      occurrenceConnectorKind source target.1 target.2 = .fixedRed)
    (element : FixedRedInternalGreen) :
    (occurrenceTriples source current.1 current.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.fixedRedInternal target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        ((fixedRedPhysicalGreen element).neighbors).map fun triple =>
          ⟨.fixedRed target.1 target.2 triple, (0, 0)⟩
      else
        [] := by
  rcases current with ⟨currentAtom, currentSlot⟩
  rcases target with ⟨targetAtom, targetSlot⟩
  by_cases sameAtom : currentAtom = targetAtom
  · subst currentAtom
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases element <;>
        simp_all [occurrenceTriples, allFixedRedTriples,
          tripleReferences, fixedRedTripleReferences,
          FixedRedConnectorTriple.references,
          fixedRedGreenElement, fixedRedPhysicalGreen,
          FixedRedConnectorGreen.neighbors, greenClauseTerminal]
    · cases currentKind :
          occurrenceConnectorKind source targetAtom currentSlot <;>
        cases element <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryGreenElement, fixedRedGreenElement,
          greenClauseTerminal]
  · cases currentKind :
        occurrenceConnectorKind source currentAtom currentSlot <;>
      cases element <;>
      simp_all [occurrenceTriples, allOrdinaryTriples,
        allFixedRedTriples, tripleReferences,
        ordinaryTripleReferences, fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryGreenElement, fixedRedGreenElement,
        greenClauseTerminal]

set_option maxHeartbeats 800000 in
theorem occurrenceBlock_blueFixedRed_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable × OccurrenceSlot)
    (kindEq :
      occurrenceConnectorKind source target.1 target.2 = .fixedRed)
    (element : FixedRedInternalBlue) :
    (occurrenceTriples source current.1 current.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.fixedRedInternal target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        ((fixedRedPhysicalBlue element).neighbors).map fun triple =>
          ⟨.fixedRed target.1 target.2 triple, (0, 0)⟩
      else
        [] := by
  rcases current with ⟨currentAtom, currentSlot⟩
  rcases target with ⟨targetAtom, targetSlot⟩
  by_cases sameAtom : currentAtom = targetAtom
  · subst currentAtom
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases element <;>
        simp_all [occurrenceTriples, allFixedRedTriples,
          tripleReferences, fixedRedTripleReferences,
          FixedRedConnectorTriple.references,
          fixedRedBlueElement, fixedRedPhysicalBlue,
          FixedRedConnectorBlue.neighbors, blueClauseTerminal]
    · cases currentKind :
          occurrenceConnectorKind source targetAtom currentSlot <;>
        cases element <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryBlueElement, fixedRedBlueElement,
          blueClauseTerminal]
  · cases currentKind :
        occurrenceConnectorKind source currentAtom currentSlot <;>
      cases element <;>
      simp_all [occurrenceTriples, allOrdinaryTriples,
        allFixedRedTriples, tripleReferences,
        ordinaryTripleReferences, fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryBlueElement, fixedRedBlueElement,
        blueClauseTerminal]

theorem clauseTriples_redFixedRed_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (target : Variable × OccurrenceSlot)
    (element : FixedRedInternalRed) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom =
              RedElement.fixedRedInternal
                target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseRedElement, X3CClauseSet.coloredReferences]

theorem clauseTriples_greenFixedRed_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (target : Variable × OccurrenceSlot)
    (element : FixedRedInternalGreen) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.fixedRedInternal
                target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseGreenElement, X3CClauseSet.coloredReferences]

theorem clauseTriples_blueFixedRed_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (target : Variable × OccurrenceSlot)
    (element : FixedRedInternalBlue) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.fixedRedInternal
                target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseBlueElement, X3CClauseSet.coloredReferences]

theorem problem_redIncidences_fixedRedInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalRed) :
    (problem source).redIncidences
        (.fixedRedInternal atom slot element) =
      ((fixedRedPhysicalRed element).neighbors).map fun triple =>
        ⟨.fixedRed atom slot triple, (0, 0)⟩ := by
  rw [TypedProblem.redIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom =
              RedElement.fixedRedInternal atom slot element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_redFixedRed_filterMap_nil
      source (atom, slot) element,
    List.append_nil,
    variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [occurrenceBlock_redFixedRed_filterMap
    source _ (atom, slot) kindEq element]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (occurrenceEntries source) (atom, slot)
      (((fixedRedPhysicalRed element).neighbors).map fun triple =>
        (⟨.fixedRed atom slot triple, (0, 0)⟩ :
          Incidence Variable))
      (occurrenceEntries_nodup source)
      ((mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩)

theorem problem_greenIncidences_fixedRedInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalGreen) :
    (problem source).greenIncidences
        (.fixedRedInternal atom slot element) =
      ((fixedRedPhysicalGreen element).neighbors).map fun triple =>
        ⟨.fixedRed atom slot triple, (0, 0)⟩ := by
  rw [TypedProblem.greenIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.fixedRedInternal atom slot element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_greenFixedRed_filterMap_nil
      source (atom, slot) element,
    List.append_nil,
    variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [occurrenceBlock_greenFixedRed_filterMap
    source _ (atom, slot) kindEq element]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (occurrenceEntries source) (atom, slot)
      (((fixedRedPhysicalGreen element).neighbors).map fun triple =>
        (⟨.fixedRed atom slot triple, (0, 0)⟩ :
          Incidence Variable))
      (occurrenceEntries_nodup source)
      ((mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩)

theorem problem_blueIncidences_fixedRedInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalBlue) :
    (problem source).blueIncidences
        (.fixedRedInternal atom slot element) =
      ((fixedRedPhysicalBlue element).neighbors).map fun triple =>
        ⟨.fixedRed atom slot triple, (0, 0)⟩ := by
  rw [TypedProblem.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.fixedRedInternal atom slot element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_blueFixedRed_filterMap_nil
      source (atom, slot) element,
    List.append_nil,
    variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [occurrenceBlock_blueFixedRed_filterMap
    source _ (atom, slot) kindEq element]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (occurrenceEntries source) (atom, slot)
      (((fixedRedPhysicalBlue element).neighbors).map fun triple =>
        (⟨.fixedRed atom slot triple, (0, 0)⟩ :
          Incidence Variable))
      (occurrenceEntries_nodup source)
      ((mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩)

/-- Every private element of a listed fixed-red detour has degree two in the
global assembly. -/
theorem fixedRedPrivate_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed) :
    (∀ element : FixedRedInternalRed,
        ((problem source).redIncidences
          (.fixedRedInternal atom slot element)).length = 2) ∧
      (∀ element : FixedRedInternalGreen,
        ((problem source).greenIncidences
          (.fixedRedInternal atom slot element)).length = 2) ∧
      (∀ element : FixedRedInternalBlue,
        ((problem source).blueIncidences
          (.fixedRedInternal atom slot element)).length = 2) := by
  constructor
  · intro element
    rw [problem_redIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
    cases element <;> rfl
  constructor
  · intro element
    rw [problem_greenIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
    cases element <;> rfl
  · intro element
    rw [problem_blueIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
    cases element <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
