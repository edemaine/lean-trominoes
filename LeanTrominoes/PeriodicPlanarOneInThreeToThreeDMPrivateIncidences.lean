/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration
import LeanTrominoes.PeriodicOneInThreeToThreeDMVariableIncidences

/-!
# Private-element incidences in the planar periodic 3DM assembly

Each ordinary connector has one private green and one private blue
degree-two element.  Each fixed-red detour has eight private degree-two
elements.  This file localizes the global incidence filters to the unique
variable/slot block that owns each such element.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

def ordinaryGreenPrivate :
    VariableOccurrenceVariant → OrdinaryInternal
  | .fixedGreen => .cycleShared
  | .fixedBlue => .cycleShared

def ordinaryBluePrivate :
    VariableOccurrenceVariant → OrdinaryInternal
  | .fixedGreen => .auxiliaryShared
  | .fixedBlue => .auxiliaryShared

def ordinaryGreenPrivateNeighbors :
    VariableOccurrenceVariant → List VariableOccurrenceTriple
  | .fixedGreen => [.first, .second]
  | .fixedBlue => [.first, .second]

def ordinaryBluePrivateNeighbors :
    VariableOccurrenceVariant → List VariableOccurrenceTriple
  | .fixedGreen => [.second, .auxiliary]
  | .fixedBlue => [.second, .auxiliary]

/-- One occurrence block contributes the expected ordinary private-green
incidences exactly when its module entry is the target. -/
theorem occurrenceBlock_greenOrdinary_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable × OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source target.1 target.2 =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    (occurrenceTriples source current.1 current.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.ordinaryInternal target.1 target.2
                (ordinaryGreenPrivate variant) then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        (ordinaryGreenPrivateNeighbors variant).map fun triple =>
          ⟨.ordinary target.1 target.2 variant triple, (0, 0)⟩
      else
        [] := by
  rcases current with ⟨currentAtom, currentSlot⟩
  rcases target with ⟨targetAtom, targetSlot⟩
  by_cases sameAtom : currentAtom = targetAtom
  · subst currentAtom
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases variant <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          tripleReferences, ordinaryTripleReferences,
          VariableOccurrenceTriple.references,
          ordinaryGreenElement, greenClauseTerminal,
          ordinaryGreenPrivate,
          ordinaryGreenPrivateNeighbors]
    · cases currentKind :
          occurrenceConnectorKind source targetAtom currentSlot <;>
        cases variant <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryGreenElement, fixedRedGreenElement,
          greenClauseTerminal,
          ordinaryGreenPrivate]
  · cases currentKind :
        occurrenceConnectorKind source currentAtom currentSlot <;>
      cases variant <;>
      simp_all [occurrenceTriples, allOrdinaryTriples,
        allFixedRedTriples, tripleReferences,
        ordinaryTripleReferences, fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryGreenElement, fixedRedGreenElement,
        greenClauseTerminal,
        ordinaryGreenPrivate]

/-- One occurrence block contributes the expected ordinary private-blue
incidences exactly at its target entry. -/
theorem occurrenceBlock_blueOrdinary_filterMap
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable × OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source target.1 target.2 =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    (occurrenceTriples source current.1 current.2).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.ordinaryInternal target.1 target.2
                (ordinaryBluePrivate variant) then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        (ordinaryBluePrivateNeighbors variant).map fun triple =>
          ⟨.ordinary target.1 target.2 variant triple, (0, 0)⟩
      else
        [] := by
  rcases current with ⟨currentAtom, currentSlot⟩
  rcases target with ⟨targetAtom, targetSlot⟩
  by_cases sameAtom : currentAtom = targetAtom
  · subst currentAtom
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases variant <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          tripleReferences, ordinaryTripleReferences,
          VariableOccurrenceTriple.references,
          ordinaryBlueElement, blueClauseTerminal,
          ordinaryBluePrivate,
          ordinaryBluePrivateNeighbors]
    · cases currentKind :
          occurrenceConnectorKind source targetAtom currentSlot <;>
        cases variant <;>
        simp_all [occurrenceTriples, allOrdinaryTriples,
          allFixedRedTriples, tripleReferences,
          ordinaryTripleReferences, fixedRedTripleReferences,
          VariableOccurrenceTriple.references,
          FixedRedConnectorTriple.references,
          ordinaryBlueElement, fixedRedBlueElement,
          blueClauseTerminal,
          ordinaryBluePrivate]
  · cases currentKind :
        occurrenceConnectorKind source currentAtom currentSlot <;>
      cases variant <;>
      simp_all [occurrenceTriples, allOrdinaryTriples,
        allFixedRedTriples, tripleReferences,
        ordinaryTripleReferences, fixedRedTripleReferences,
        VariableOccurrenceTriple.references,
        FixedRedConnectorTriple.references,
        ordinaryBlueElement, fixedRedBlueElement,
        blueClauseTerminal,
        ordinaryBluePrivate]

/-- Clause blocks cannot meet an ordinary private element. -/
theorem clauseTriples_greenOrdinary_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (target : Variable × OccurrenceSlot)
    (element : OrdinaryInternal) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.ordinaryInternal
                target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseGreenElement, X3CClauseSet.coloredReferences]

theorem clauseTriples_blueOrdinary_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (target : Variable × OccurrenceSlot)
    (element : OrdinaryInternal) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.ordinaryInternal
                target.1 target.2 element then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseBlueElement, X3CClauseSet.coloredReferences]

/-- Global private-green incidences of an ordinary connector are exactly its
two local neighbors. -/
theorem problem_greenIncidences_ordinaryInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    (problem source).greenIncidences
        (.ordinaryInternal atom slot
          (ordinaryGreenPrivate variant)) =
      (ordinaryGreenPrivateNeighbors variant).map fun triple =>
        ⟨.ordinary atom slot variant triple, (0, 0)⟩ := by
  rw [TypedProblem.greenIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).green
          if reference.atom =
              GreenElement.ordinaryInternal atom slot
                (ordinaryGreenPrivate variant) then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_greenOrdinary_filterMap_nil
      source (atom, slot) (ordinaryGreenPrivate variant),
    List.append_nil,
    variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [occurrenceBlock_greenOrdinary_filterMap
    source _ (atom, slot) variant kindEq]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (occurrenceEntries source) (atom, slot)
      ((ordinaryGreenPrivateNeighbors variant).map fun triple =>
        (⟨.ordinary atom slot variant triple, (0, 0)⟩ :
          Incidence Variable))
      (occurrenceEntries_nodup source)
      ((mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩)

/-- Global private-blue incidences of an ordinary connector are exactly its
two local neighbors. -/
theorem problem_blueIncidences_ordinaryInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    (problem source).blueIncidences
        (.ordinaryInternal atom slot
          (ordinaryBluePrivate variant)) =
      (ordinaryBluePrivateNeighbors variant).map fun triple =>
        ⟨.ordinary atom slot variant triple, (0, 0)⟩ := by
  rw [TypedProblem.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.ordinaryInternal atom slot
                (ordinaryBluePrivate variant) then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_blueOrdinary_filterMap_nil
      source (atom, slot) (ordinaryBluePrivate variant),
    List.append_nil,
    variableTriples_eq_occurrenceEntries_flatMap,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [occurrenceBlock_blueOrdinary_filterMap
    source _ (atom, slot) variant kindEq]
  exact
    PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
      (occurrenceEntries source) (atom, slot)
      ((ordinaryBluePrivateNeighbors variant).map fun triple =>
        (⟨.ordinary atom slot variant triple, (0, 0)⟩ :
          Incidence Variable))
      (occurrenceEntries_nodup source)
      ((mem_occurrenceEntries_iff source atom slot).mpr
        ⟨atomMember, slotMember⟩)

/-- Both ordinary private colored elements have degree two. -/
theorem ordinaryPrivate_degrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    ((problem source).greenIncidences
        (.ordinaryInternal atom slot
          (ordinaryGreenPrivate variant))).length = 2 ∧
      ((problem source).blueIncidences
        (.ordinaryInternal atom slot
          (ordinaryBluePrivate variant))).length = 2 := by
  rw [problem_greenIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq,
    problem_blueIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq]
  cases variant <;>
    simp [ordinaryGreenPrivateNeighbors,
      ordinaryBluePrivateNeighbors]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
