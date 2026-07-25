import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseInternalIncidences

/-!
# Variable-cycle link incidences in the planar periodic 3DM assembly

Every used occurrence slot declares one red cycle-link element.  Positive
and negative occurrences may exchange their two physical continuation
ports, but the assembled cycle still gives every link exactly two
incidences.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

/-- Incidences of one target cycle link contributed by one occurrence
module. -/
def occurrenceCycleLinkIncidences {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (current target : OccurrenceSlot) :
    List (Incidence Variable) :=
  (occurrenceTriples source atom current).filterMap fun triple =>
    let reference := (tripleReferences source triple).red
    if reference.atom = RedElement.cycleLink atom target then
      some ⟨triple, reference.offset⟩
    else none

/-- A module contributes one incidence for each of its first and second
logical continuation slots that equals the target. -/
theorem occurrenceCycleLinkIncidences_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (current target : OccurrenceSlot) :
    (occurrenceCycleLinkIncidences
      source atom current target).length =
      (if firstCycleLinkSlot source atom current = target then 1 else 0) +
      (if secondCycleLinkSlot source atom current = target then 1 else 0) := by
  by_cases firstEq :
      firstCycleLinkSlot source atom current = target <;>
    by_cases secondEq :
      secondCycleLinkSlot source atom current = target <;>
    cases kindEq :
      occurrenceConnectorKind source atom current <;>
    simp_all [occurrenceCycleLinkIncidences, occurrenceTriples,
      allOrdinaryTriples, allFixedRedTriples,
      tripleReferences, ordinaryTripleReferences,
      fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement, redClauseTerminal]

/- The complete used-slot cycle around one atom gives every one of its
links exactly two incidences. -/
set_option maxHeartbeats 800000 in
theorem occurrenceCycleLinkIncidencesForAtom_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (target : OccurrenceSlot)
    (targetMember : target ∈ usedSlots source atom) :
    ((usedSlots source atom).flatMap fun current =>
      occurrenceCycleLinkIncidences
        source atom current target).length = 2 := by
  rw [List.length_flatMap]
  simp_rw [occurrenceCycleLinkIncidences_length]
  cases target <;>
    cases firstLookup : occurrenceAt source atom .first <;>
    cases secondLookup : occurrenceAt source atom .second <;>
    cases thirdLookup : occurrenceAt source atom .third <;>
    cases firstPolarity :
      occurrencePolarity source atom .first <;>
    cases secondPolarity :
      occurrencePolarity source atom .second <;>
    cases thirdPolarity :
      occurrencePolarity source atom .third <;>
    simp_all [usedSlots, allOccurrenceSlots,
      PeriodicOneInThreeToThreeDM.OccurrenceSlot.all,
      firstCycleLinkSlot, secondCycleLinkSlot,
      nextUsedSlot]

/-- An occurrence module of another source atom cannot meet the target
atom's cycle link. -/
theorem occurrenceBlock_redCycleLink_filterMap_nil_of_ne
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (current target : Variable) (different : current ≠ target)
    (slot targetSlot : OccurrenceSlot) :
    (occurrenceTriples source current slot).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.cycleLink target targetSlot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  cases kindEq : occurrenceConnectorKind source current slot <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples, tripleReferences,
      ordinaryTripleReferences, fixedRedTripleReferences,
      VariableOccurrenceTriple.references,
      FixedRedConnectorTriple.references,
      ordinaryRedElement, fixedRedRedElement,
      redClauseTerminal, different]

/-- Clause triples cannot meet a variable-cycle link. -/
theorem clauseTriples_redCycleLink_filterMap_nil
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (clauseTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.cycleLink atom slot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none) = [] := by
  rw [clauseTriples,
    PeriodicOneInThreeToThreeDM.filterMap_flatMap]
  simp [allClauseSets, List.filterMap_map,
    tripleReferences, clauseTripleReferences,
    clauseRedElement, X3CClauseSet.coloredReferences]

/-- A used cycle-link element has degree two in the global assembly. -/
theorem problem_redIncidences_cycleLink_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    ((problem source).redIncidences
      (.cycleLink atom slot)).length = 2 := by
  rw [TypedProblem.redIncidences]
  change
    ((triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).red
          if reference.atom = RedElement.cycleLink atom slot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else none)).length = 2
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
  rw [PeriodicOneInThreeToThreeDM.flatMap_if_eq_of_nodup
    (occurringVariables source) atom
    ((usedSlots source atom).flatMap fun current =>
      occurrenceCycleLinkIncidences source atom current slot)
    (PeriodicOneInThreeToThreeDM.occurringVariables_nodup source)
    atomMember]
  exact occurrenceCycleLinkIncidencesForAtom_length
    source atom slot slotMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
