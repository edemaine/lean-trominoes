import LeanTrominoes.PeriodicOneInThreeToThreeDMBlueComplementIncidences

/-!
# Unused occurrence-pair blue incidences

When a variable occurs fewer than three times, each unassigned occurrence
slot receives a private blue cap.  Its incidence list is exactly the two
complementary ports in that slot, both at zero offset.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Filtering one occurrence pair at a selected private unused cap retains
both ports exactly when both the variable and slot agree. -/
theorem variablePair_filterMap_unused {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (current target : Variable)
    (currentSlot targetSlot : OccurrenceSlot)
    (unused : occurrenceAt source target targetSlot = none) :
    ((OccurrenceSlot.triples currentSlot).map
        (Triple.variable current)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.unused target targetSlot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target ∧ currentSlot = targetSlot then
        (OccurrenceSlot.triples targetSlot).map fun triple =>
          ⟨.variable target triple, (0, 0)⟩
      else
        [] := by
  by_cases sameAtom : current = target
  · subst current
    by_cases sameSlot : currentSlot = targetSlot
    · subst currentSlot
      cases targetSlot <;>
        simp [OccurrenceSlot.triples, tripleReferences,
          variableTripleReferences, variableBlueElement,
          variableBlueOffset, unused]
    · cases lookup :
        occurrenceAt source target currentSlot with
      | none =>
          cases currentSlot <;> cases targetSlot <;>
            simp_all [OccurrenceSlot.triples, tripleReferences,
              variableTripleReferences, variableBlueElement,
              variableBlueOffset]
      | some tagged =>
          cases value : tagged.1.value <;>
            cases currentSlot <;> cases targetSlot <;>
            simp_all [OccurrenceSlot.triples, tripleReferences,
              variableTripleReferences, variableBlueElement,
              variableBlueOffset]
  · cases lookup :
      occurrenceAt source current currentSlot with
    | none =>
        cases currentSlot <;> cases targetSlot <;>
          simp_all [OccurrenceSlot.triples, tripleReferences,
            variableTripleReferences, variableBlueElement,
            variableBlueOffset]
    | some tagged =>
        cases value : tagged.1.value <;>
          cases currentSlot <;> cases targetSlot <;>
          simp_all [OccurrenceSlot.triples, tripleReferences,
            variableTripleReferences, variableBlueElement,
            variableBlueOffset]

/-- Filtering one six-cycle variable block at a selected private unused cap
retains exactly the selected slot's two ports when the atom agrees. -/
theorem variableBlock_filterMap_unused {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (current target : Variable) (targetSlot : OccurrenceSlot)
    (unused : occurrenceAt source target targetSlot = none) :
    (allVariableTriples.map (Triple.variable current)).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom =
              BlueElement.unused target targetSlot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) =
      if current = target then
        (OccurrenceSlot.triples targetSlot).map fun triple =>
          ⟨.variable target triple, (0, 0)⟩
      else
        [] := by
  rw [allVariableTriples_eq_slotTriples, List.map_flatMap,
    filterMap_flatMap]
  simp_rw [variablePair_filterMap_unused
    source current target _ targetSlot unused]
  by_cases sameAtom : current = target
  · subst current
    simp only [true_and, if_true]
    exact flatMap_if_eq_of_nodup
      OccurrenceSlot.all targetSlot
      ((OccurrenceSlot.triples targetSlot).map fun triple =>
        (⟨.variable target triple, (0, 0)⟩ :
          Incidence Variable))
      (by decide)
      (by cases targetSlot <;> simp [OccurrenceSlot.all])
  · simp [sameAtom]

/-- Clause-auxiliary triples never meet a private unused blue cap. -/
theorem blueClauseAuxiliaries_filterMap_unused_nil {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot) :
    (clauseAuxiliaryTriples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.unused atom slot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = [] := by
  simp [clauseAuxiliaryTriples, tripleReferences,
    clauseAuxiliaryReferences]

/-- A listed unused slot exposes exactly its two complementary variable
ports, both at zero offset. -/
theorem problem_blueIncidences_unused {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot)
    (unused : occurrenceAt source atom slot = none) :
    (problem source).blueIncidences (.unused atom slot) =
      (OccurrenceSlot.triples slot).map fun triple =>
        ⟨.variable atom triple, (0, 0)⟩ := by
  rw [TypedPeriodicThreeDM.blueIncidences]
  change
    (triples source).filterMap
        (fun triple =>
          let reference := (tripleReferences source triple).blue
          if reference.atom = BlueElement.unused atom slot then
            some (⟨triple, reference.offset⟩ : Incidence Variable)
          else
            none) = _
  rw [triples, List.filterMap_append,
    blueClauseAuxiliaries_filterMap_unused_nil, List.append_nil,
    variableTriples, filterMap_flatMap]
  simp_rw [variableBlock_filterMap_unused
    source _ atom slot unused]
  exact flatMap_if_eq_of_nodup
    (occurringVariables source) atom
    ((OccurrenceSlot.triples slot).map fun triple =>
      (⟨.variable atom triple, (0, 0)⟩ :
        Incidence Variable))
    (occurringVariables_nodup source) atomMember

/-- Values at a private unused cap are exactly the selections of its two
complementary ports at the same cell. -/
theorem problem_blueIncidentValues_unused {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot)
    (unused : occurrenceAt source atom slot = none)
    (cell : Cell) :
    (problem source).blueIncidentValues assignment
        (.unused atom slot) cell =
      (OccurrenceSlot.triples slot).map fun triple =>
        assignment (.variable atom triple) cell := by
  rw [TypedPeriodicThreeDM.blueIncidentValues,
    problem_blueIncidences_unused
      source atom atomMember slot unused]
  simp [TypedPeriodicThreeDM.incidenceValue, Cell.sub]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
