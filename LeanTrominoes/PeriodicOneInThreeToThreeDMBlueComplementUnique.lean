import LeanTrominoes.PeriodicOneInThreeToThreeDMBlueUnusedIncidences

/-!
# Uniqueness of complementary blue incidences

Tagged clause/literal positions are unique.  Consequently, once a genuine
tagged occurrence is assigned to a variable slot, its private complement
blue element has exactly two incidences: the opposite variable port and the
matching clause auxiliary.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- A `filterMap` selecting a key absent from the mapped key list is empty. -/
theorem filterMap_key_eq_nil_of_not_mem
    {Element Key Output : Type*} [DecidableEq Key]
    (values : List Element) (key : Element → Key)
    (target : Key) (output : Output)
    (notMember : target ∉ values.map key) :
    values.filterMap
        (fun value =>
          if key value = target then some output else none) = [] := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at notMember
      have headNe : key head ≠ target :=
        fun same => notMember.1 same.symm
      simp [headNe, induction notMember.2]

/-- Filtering by the key of a selected list member yields one copy of a
constant output when the key projection is duplicate-free. -/
theorem filterMap_key_eq_singleton {Element Key Output : Type*}
    [DecidableEq Key] (values : List Element) (key : Element → Key)
    (selected : Element) (output : Output)
    (keysNodup : (values.map key).Nodup)
    (selectedMember : selected ∈ values) :
    values.filterMap
        (fun value =>
          if key value = key selected then some output else none) =
      [output] := by
  induction values with
  | nil => simp at selectedMember
  | cons head tail induction =>
      rw [List.map_cons, List.nodup_cons] at keysNodup
      simp only [List.mem_cons] at selectedMember
      rcases selectedMember with selectedEq | selectedTail
      · subst selected
        have tailNil :=
          filterMap_key_eq_nil_of_not_mem
            tail key (key head) output keysNodup.1
        simp [tailNil]
      · have headNe : key head ≠ key selected := by
          intro same
          exact keysNodup.1
            (List.mem_map.mpr
              ⟨selected, selectedTail, same.symm⟩)
        simp [headNe,
          induction keysNodup.2 selectedTail]

/-- Tagged occurrences with the same clause/literal position are equal. -/
theorem taggedOccurrence_eq_of_position_eq {Variable : Type*}
    (source : PeriodicCNF Variable)
    (first second : TaggedOccurrence Variable)
    (firstMember :
      first ∈ PeriodicThreeSATThree.taggedLiterals source)
    (secondMember :
      second ∈ PeriodicThreeSATThree.taggedLiterals source)
    (sameClause : first.2.1 = second.2.1)
    (sameLiteral : first.2.2 = second.2.2) :
    first = second := by
  rcases first with ⟨firstLiteral, firstClauseIndex,
    firstLiteralIndex⟩
  rcases second with ⟨secondLiteral, secondClauseIndex,
    secondLiteralIndex⟩
  simp only at sameClause sameLiteral
  subst secondClauseIndex
  subst secondLiteralIndex
  have firstLookup :=
    literalAt_eq_some_of_tagged_mem source
      (firstLiteral, firstClauseIndex, firstLiteralIndex)
      firstMember
  have secondLookup :=
    literalAt_eq_some_of_tagged_mem source
      (secondLiteral, firstClauseIndex, firstLiteralIndex)
      secondMember
  rw [firstLookup] at secondLookup
  injection secondLookup with literalEq
  change firstLiteral = secondLiteral at literalEq
  subst secondLiteral
  rfl

/-- A selected tagged position contributes exactly one clause-auxiliary
incidence to its private complementary blue element. -/
theorem complementAuxiliaryIncidences_eq_singleton_of_tagged_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source) :
    complementAuxiliaryIncidences source tagged.2.1 tagged.2.2 =
      [⟨.clauseAuxiliary tagged.2.1 tagged.2.2,
        (0, 0)⟩] := by
  unfold complementAuxiliaryIncidences
  have filtered :=
    filterMap_key_eq_singleton
      (PeriodicThreeSATThree.taggedLiterals source)
      (fun current => (current.2.1, current.2.2))
      tagged
      (⟨.clauseAuxiliary tagged.2.1 tagged.2.2,
        (0, 0)⟩ : Incidence Variable)
      (by
        rw [taggedLiterals_positions]
        exact
          PeriodicThreeSATThree.occurrenceIndicesFrom_nodup
            0 source.clauses)
      member
  simpa only [Prod.mk.injEq] using filtered

/-- Relative to one genuine assigned slot, every slot/atom contribution to
that tagged position is empty except for the selected opposite port. -/
theorem complementIncidenceAt_eq_target {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (targetSlot : OccurrenceSlot)
    (targetLookup :
      occurrenceAt source tagged.1.atom targetSlot = some tagged)
    (current : Variable) (currentSlot : OccurrenceSlot) :
    complementIncidenceAt source current currentSlot
        tagged.2.1 tagged.2.2 =
      if current = tagged.1.atom ∧ currentSlot = targetSlot then
        [⟨.variable tagged.1.atom
            (targetSlot.complementTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩]
      else
        [] := by
  cases currentLookup :
      occurrenceAt source current currentSlot with
  | none =>
      have different :
          ¬(current = tagged.1.atom ∧ currentSlot = targetSlot) := by
        rintro ⟨rfl, rfl⟩
        rw [targetLookup] at currentLookup
        contradiction
      simp [complementIncidenceAt, currentLookup, different]
  | some currentTagged =>
      have currentData :=
        occurrenceAt_mem_and_atom source current currentSlot
          currentTagged currentLookup
      by_cases samePosition :
          currentTagged.2.1 = tagged.2.1 ∧
            currentTagged.2.2 = tagged.2.2
      · have taggedEq :=
          taggedOccurrence_eq_of_position_eq source
            currentTagged tagged currentData.1 member
            samePosition.1 samePosition.2
        subst currentTagged
        have atomEq : current = tagged.1.atom :=
          currentData.2.symm
        subst current
        have slotEq :=
          occurrenceAt_slot_unique source tagged.1.atom tagged
            currentSlot targetSlot currentLookup targetLookup
        subst currentSlot
        simp [complementIncidenceAt, targetLookup]
      · have different :
          ¬(current = tagged.1.atom ∧
            currentSlot = targetSlot) := by
          rintro ⟨rfl, rfl⟩
          rw [targetLookup] at currentLookup
          injection currentLookup with taggedEq
          subst currentTagged
          exact samePosition ⟨rfl, rfl⟩
        simp [complementIncidenceAt, currentLookup,
          samePosition, different]

/-- One variable block contributes the selected opposite port exactly when
its atom agrees with the tagged occurrence. -/
theorem complementIncidencesForAtom_eq_target {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (targetSlot : OccurrenceSlot)
    (targetLookup :
      occurrenceAt source tagged.1.atom targetSlot = some tagged)
    (current : Variable) :
    complementIncidencesForAtom source current
        tagged.2.1 tagged.2.2 =
      if current = tagged.1.atom then
        [⟨.variable tagged.1.atom
            (targetSlot.complementTriple tagged.1.value),
          reverseOffset tagged.1.offset⟩]
      else
        [] := by
  unfold complementIncidencesForAtom
  simp_rw [complementIncidenceAt_eq_target
    source tagged member targetSlot targetLookup current]
  by_cases sameAtom : current = tagged.1.atom
  · subst current
    simp only [true_and, if_true]
    exact flatMap_if_eq_of_nodup
      OccurrenceSlot.all targetSlot
      ([⟨.variable tagged.1.atom
          (targetSlot.complementTriple tagged.1.value),
        reverseOffset tagged.1.offset⟩] :
        List (Incidence Variable))
      (by decide)
      (by cases targetSlot <;> simp [OccurrenceSlot.all])
  · simp [sameAtom]

/-- The complete variable-port part for a genuine tagged occurrence is the
single opposite port assigned to that occurrence's slot. -/
theorem complementVariableIncidences_eq_singleton_of_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (slot : OccurrenceSlot)
    (lookup :
      occurrenceAt source tagged.1.atom slot = some tagged) :
    complementVariableIncidences source tagged.2.1 tagged.2.2 =
      [⟨.variable tagged.1.atom
          (slot.complementTriple tagged.1.value),
        reverseOffset tagged.1.offset⟩] := by
  unfold complementVariableIncidences
  simp_rw [complementIncidencesForAtom_eq_target
    source tagged member slot lookup]
  exact flatMap_if_eq_of_nodup
    (occurringVariables source) tagged.1.atom
    ([⟨.variable tagged.1.atom
        (slot.complementTriple tagged.1.value),
      reverseOffset tagged.1.offset⟩] :
      List (Incidence Variable))
    (occurringVariables_nodup source)
    (atom_mem_occurringVariables_of_tagged_mem
      source tagged member)

/-- A genuine occurrence-specific complementary blue element has degree
exactly two, with its opposite variable port followed by its auxiliary. -/
theorem problem_blueIncidences_complement_of_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (slot : OccurrenceSlot)
    (lookup :
      occurrenceAt source tagged.1.atom slot = some tagged) :
    (problem source).blueIncidences
        (.complement tagged.2.1 tagged.2.2) =
      [⟨.variable tagged.1.atom
          (slot.complementTriple tagged.1.value),
        reverseOffset tagged.1.offset⟩,
        ⟨.clauseAuxiliary tagged.2.1 tagged.2.2,
          (0, 0)⟩] := by
  rw [problem_blueIncidences_complement,
    complementVariableIncidences_eq_singleton_of_lookup
      source tagged member slot lookup,
    complementAuxiliaryIncidences_eq_singleton_of_tagged_mem
      source tagged member]
  rfl

/-- Values at a genuine complementary blue element are the opposite variable
port at the literal cell and the auxiliary at the clause cell. -/
theorem problem_blueIncidentValues_complement_of_lookup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : (problem source).MatchingAssignment)
    (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (slot : OccurrenceSlot)
    (lookup :
      occurrenceAt source tagged.1.atom slot = some tagged)
    (cell : Cell) :
    (problem source).blueIncidentValues assignment
        (.complement tagged.2.1 tagged.2.2) cell =
      [assignment
          (.variable tagged.1.atom
            (slot.complementTriple tagged.1.value))
          (Cell.add cell tagged.1.offset),
        assignment
          (.clauseAuxiliary tagged.2.1 tagged.2.2) cell] := by
  rw [TypedPeriodicThreeDM.blueIncidentValues,
    problem_blueIncidences_complement_of_lookup
      source tagged member slot lookup]
  simp only [List.map_cons, List.map_nil,
    TypedPeriodicThreeDM.incidenceValue, sub_reverseOffset]
  simp [Cell.sub]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
