/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTerminalCovers

/-!
# Canonical exact cover of variable-cycle links

Irrespective of literal polarity and connector implementation, one
occurrence module contributes the variable phase to its own cycle link and
the complementary phase to its cyclic successor.  Hence every used link
receives exactly one selected incidence.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/- The complete red incidence list of a used cycle link is exactly the
flattened list of contributions from that variable's occurrence modules. -/
set_option maxHeartbeats 800000 in
theorem problem_redIncidences_cycleLink
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) :
    (problem source).redIncidences (.cycleLink atom slot) =
      (usedSlots source atom).flatMap fun current =>
        occurrenceCycleLinkIncidences source atom current slot := by
  rw [TypedProblem.redIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.cycleLink atom slot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = _
  rw [triples, List.filterMap_append,
    clauseTriples_redCycleLink_filterMap_nil,
    List.append_nil, variableTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp_rw [PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  have targetBlock :
      ((usedSlots source atom).flatMap fun current =>
        (occurrenceTriples source atom current).filterMap
          (fun triple =>
            let reference := (tripleReferences source triple).red
            if reference.atom =
                RedElement.cycleLink atom slot then
              some (⟨triple, reference.offset⟩ :
                Incidence Variable)
            else none)) =
        (usedSlots source atom).flatMap fun current =>
          occurrenceCycleLinkIncidences source atom current slot := by
    rfl
  have atomBlock (current : Variable) :
      ((usedSlots source current).flatMap fun currentSlot =>
        (occurrenceTriples source current currentSlot).filterMap
          (fun triple =>
            let reference := (tripleReferences source triple).red
            if reference.atom =
                RedElement.cycleLink atom slot then
              some (⟨triple, reference.offset⟩ :
                Incidence Variable)
            else none)) =
        if current = atom then
          (usedSlots source atom).flatMap fun current =>
            occurrenceCycleLinkIncidences
              source atom current slot
        else [] := by
    by_cases same : current = atom
    · subst current
      simpa using targetBlock
    · simp [same,
        occurrenceBlock_redCycleLink_filterMap_nil_of_ne
          source current atom same]
  simp_rw [atomBlock]
  exact PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
    (occurringVariables source) atom
    ((usedSlots source atom).flatMap fun current =>
      occurrenceCycleLinkIncidences source atom current slot)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    atomMember

set_option maxHeartbeats 500000 in
private theorem occurrenceCycleLinkIncidentValues_perm_ordinary
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (current target : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom current =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue)
    (cell : Cell) :
    List.Perm
      ((occurrenceCycleLinkIncidences
        source atom current target).map fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment) incidence cell)
      ((if current = target then [assignment atom cell] else []) ++
        (if nextUsedSlot source atom current = target then
          [!assignment atom cell] else [])) := by
  by_cases currentEq : current = target <;>
    by_cases nextEq :
      nextUsedSlot source atom current = target <;>
    cases variant <;>
    cases polarityEq :
      occurrencePolarity source atom current <;>
    cases valueEq : assignment atom cell <;>
    simp_all [occurrenceCycleLinkIncidences, occurrenceTriples,
      allOrdinaryTriples,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement, redClauseTerminal,
      firstCycleLinkSlot, secondCycleLinkSlot,
      TypedProblem.incidenceValue, Cell.sub,
      matchingOfAssignment, occurrenceSignal,
      variableConnectorLiteralSignal,
      variableOccurrenceSelection, fixedRedConnectorSelection] <;>
    decide

set_option maxHeartbeats 500000 in
private theorem occurrenceCycleLinkIncidentValues_perm_fixedRed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (current target : OccurrenceSlot)
    (kindEq :
      occurrenceConnectorKind source atom current = .fixedRed)
    (cell : Cell) :
    List.Perm
      ((occurrenceCycleLinkIncidences
        source atom current target).map fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment) incidence cell)
      ((if current = target then [assignment atom cell] else []) ++
        (if nextUsedSlot source atom current = target then
          [!assignment atom cell] else [])) := by
  by_cases currentEq : current = target <;>
    by_cases nextEq :
      nextUsedSlot source atom current = target <;>
    cases polarityEq :
      occurrencePolarity source atom current <;>
    cases valueEq : assignment atom cell <;>
    simp_all [occurrenceCycleLinkIncidences, occurrenceTriples,
      allFixedRedTriples,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement, redClauseTerminal,
      firstCycleLinkSlot, secondCycleLinkSlot,
      TypedProblem.incidenceValue, Cell.sub,
      matchingOfAssignment, occurrenceSignal,
      variableConnectorLiteralSignal,
      variableOccurrenceSelection, fixedRedConnectorSelection] <;>
    decide

/- One occurrence module's cycle-link values are, up to their physical
enumeration order, the variable phase at its own link and its complement at
the successor link. -/
theorem occurrenceCycleLinkIncidentValues_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (current target : OccurrenceSlot)
    (cell : Cell) :
    List.Perm
      ((occurrenceCycleLinkIncidences
        source atom current target).map fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment) incidence cell)
      ((if current = target then [assignment atom cell] else []) ++
        (if nextUsedSlot source atom current = target then
          [!assignment atom cell] else [])) := by
  cases kindEq :
      occurrenceConnectorKind source atom current with
  | fixedRed =>
      exact occurrenceCycleLinkIncidentValues_perm_fixedRed
        source assignment atom current target kindEq cell
  | fixedGreen =>
      exact occurrenceCycleLinkIncidentValues_perm_ordinary
        source assignment atom current target .fixedGreen kindEq cell
  | fixedBlue =>
      exact occurrenceCycleLinkIncidentValues_perm_ordinary
        source assignment atom current target .fixedBlue kindEq cell

/- Closing the used occurrence slots cyclically makes every link receive one
variable phase and one complementary phase. -/
set_option maxHeartbeats 800000 in
theorem occurrenceCycleLinkIncidentValues_exactlyOne
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (target : OccurrenceSlot)
    (targetMember : target ∈ usedSlots source atom)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      (((usedSlots source atom).flatMap fun current =>
        occurrenceCycleLinkIncidences
          source atom current target).map fun incidence =>
            (problem source).incidenceValue
              (matchingOfAssignment source assignment)
              incidence cell) := by
  rw [List.map_flatMap]
  have permutation :=
    List.Perm.flatMap_left (usedSlots source atom)
      (fun current _ =>
        occurrenceCycleLinkIncidentValues_perm
          source assignment atom current target cell)
  apply
    (PeriodicOneInThreeToThreeDM.exactlyOne_iff_of_perm
      permutation).mpr
  cases target <;>
    cases firstLookup : occurrenceAt source atom .first <;>
    cases secondLookup : occurrenceAt source atom .second <;>
    cases thirdLookup : occurrenceAt source atom .third <;>
    cases valueEq : assignment atom cell <;>
    simp_all [usedSlots, allOccurrenceSlots,
      PeriodicOneInThreeToThreeDM.OccurrenceSlot.all,
      nextUsedSlot, PeriodicOneInThree.ExactlyOne]

/-- The canonical matching covers every declared variable-cycle link. -/
theorem matchingOfAssignment_covers_cycleLink
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).redIncidentValues
        (matchingOfAssignment source assignment)
        (.cycleLink atom slot) cell) := by
  rw [TypedProblem.redIncidentValues,
    problem_redIncidences_cycleLink source atom atomMember slot]
  exact occurrenceCycleLinkIncidentValues_exactlyOne
    source assignment atom slot slotMember cell

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
