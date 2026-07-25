import LeanTrominoes.PeriodicOneInThreeToThreeDMMainClauseValues

/-!
# Completeness of the typed periodic 3DM reduction

A satisfying exact-one assignment selects the alternating variable-cycle
matching and makes every clause auxiliary repeat its source literal.  Under
the occurrence-three bound, these canonical selections cover every declared
typed red, green, and blue element exactly once.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Either alternating variable-cycle selection chooses exactly one of the
two ports in every occurrence pair. -/
theorem variableSelection_slot_exactlyOne
    (value : Bool) (slot : OccurrenceSlot) :
    PeriodicOneInThree.ExactlyOne
      ((OccurrenceSlot.triples slot).map
        (PlanarThreeDM.variableSelection value)) := by
  cases value <;> cases slot <;> decide

/-- Canonical values at either clause core are the source literal truth
values in filtered tagged-occurrence order. -/
theorem matchingOfAssignment_redIncidentValues_clause_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat) :
    (problem source).redIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate =
      (clauseOccurrences source clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1 := by
  rw [problem_redIncidentValues_clause]
  apply List.map_congr_left
  intro tagged taggedMember
  unfold clauseOccurrences at taggedMember
  rcases List.mem_filter.mp taggedMember with
    ⟨member, sameClause⟩
  have sameClauseEq : tagged.2.1 = clauseIndex := by
    simpa using sameClause
  simpa [sameClauseEq] using
    matchingOfAssignment_clauseAuxiliary
      source assignment translate tagged member

/-- The green clause core sees the same canonical source literal truth
values. -/
theorem matchingOfAssignment_greenIncidentValues_clause_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat) :
    (problem source).greenIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate =
      (clauseOccurrences source clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1 := by
  rw [problem_greenIncidentValues_clause]
  apply List.map_congr_left
  intro tagged taggedMember
  unfold clauseOccurrences at taggedMember
  rcases List.mem_filter.mp taggedMember with
    ⟨member, sameClause⟩
  have sameClauseEq : tagged.2.1 = clauseIndex := by
    simpa using sameClause
  simpa [sameClauseEq] using
    matchingOfAssignment_clauseAuxiliary
      source assignment translate tagged member

/-- A canonical matching covers every internal variable red element. -/
theorem matchingOfAssignment_covers_variable_red
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (red : PlanarThreeDM.VariableRed) (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).redIncidentValues
        (matchingOfAssignment source assignment)
        (.variable atom red) cell) := by
  rw [problem_redIncidentValues_variable
    source _ atom atomMember red cell]
  exact
    (matchingOfAssignment_variableGadgetHolds
      source assignment atom cell).1 red

/-- A canonical matching covers every internal variable green element. -/
theorem matchingOfAssignment_covers_variable_green
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (green : PlanarThreeDM.VariableGreen) (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).greenIncidentValues
        (matchingOfAssignment source assignment)
        (.variable atom green) cell) := by
  rw [problem_greenIncidentValues_variable
    source _ atom atomMember green cell]
  exact
    (matchingOfAssignment_variableGadgetHolds
      source assignment atom cell).2 green

/-- A source clause satisfying exact-one makes its canonical red clause core
covered exactly once. -/
theorem matchingOfAssignment_covers_clause_red
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds
        assignment translate clause) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).redIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate) := by
  rw [matchingOfAssignment_redIncidentValues_clause_eq]
  exact
    (exactlyOne_iff_of_perm
      (clauseOccurrences_values_perm_clauseValues
        source assignment translate clauseIndex clause
        clauseLookup)).mpr sourceHolds

/-- The same source clause satisfaction covers its canonical green core. -/
theorem matchingOfAssignment_covers_clause_green
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds
        assignment translate clause) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).greenIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate) := by
  rw [matchingOfAssignment_greenIncidentValues_clause_eq]
  exact
    (exactlyOne_iff_of_perm
      (clauseOccurrences_values_perm_clauseValues
        source assignment translate clauseIndex clause
        clauseLookup)).mpr sourceHolds

/-- Source clause satisfaction covers the canonical main clause-blue
element. -/
theorem matchingOfAssignment_covers_clause_blue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds
        assignment translate clause) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate) := by
  exact
    (exactlyOne_iff_of_perm
      (matchingOfAssignment_blueIncidentValues_clause_perm_clauseValues
        source occurrences assignment translate clauseIndex
        clause clauseLookup)).mpr sourceHolds

/-- The opposite variable port and repeated auxiliary cover every genuine
complement blue element exactly once. -/
theorem matchingOfAssignment_covers_complement_blue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (tagged : TaggedOccurrence Variable)
    (member :
      tagged ∈ PeriodicThreeSATThree.taggedLiterals source)
    (slot : OccurrenceSlot)
    (lookup :
      occurrenceAt source tagged.1.atom slot = some tagged) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.complement tagged.2.1 tagged.2.2) translate) := by
  rw [problem_blueIncidentValues_complement_of_lookup
    source _ tagged member slot lookup translate]
  rw [matchingOfAssignment_complementPort
      source assignment translate tagged.1.atom slot tagged lookup,
    matchingOfAssignment_clauseAuxiliary
      source assignment translate tagged member]
  cases PeriodicOneInThree.literalTruth
    assignment translate tagged.1 <;> decide

/-- The two canonical alternating ports cover every private unused cap exactly
once. -/
theorem matchingOfAssignment_covers_unused_blue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot)
    (unused : occurrenceAt source atom slot = none)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.unused atom slot) cell) := by
  rw [problem_blueIncidentValues_unused
    source _ atom atomMember slot unused cell]
  simpa [matchingOfAssignment] using
    variableSelection_slot_exactlyOne
      (assignment atom cell) slot

/-- Every satisfying source assignment induces a perfect matching of the
typed periodic 3DM construction. -/
theorem matchingOfAssignment_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (sourceSatisfies :
      PeriodicOneInThree.Satisfies source assignment) :
    (problem source).Satisfies
      (matchingOfAssignment source assignment) := by
  refine ⟨?_, ?_, ?_⟩
  · intro element elementMember cell
    change element ∈ redElements source at elementMember
    simp only [redElements, List.mem_append, List.mem_flatMap,
      List.mem_map] at elementMember
    rcases elementMember with
      ⟨atom, atomMember, red, redMember, rfl⟩ |
        ⟨clauseIndex, indexMember, rfl⟩
    · exact matchingOfAssignment_covers_variable_red
        source assignment atom atomMember red cell
    · have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      exact matchingOfAssignment_covers_clause_red
        source assignment cell clauseIndex clause clauseLookup
        (sourceSatisfies cell clause
          (List.getElem_mem indexLt))
  · intro element elementMember cell
    change element ∈ greenElements source at elementMember
    simp only [greenElements, List.mem_append, List.mem_flatMap,
      List.mem_map] at elementMember
    rcases elementMember with
      ⟨atom, atomMember, green, greenMember, rfl⟩ |
        ⟨clauseIndex, indexMember, rfl⟩
    · exact matchingOfAssignment_covers_variable_green
        source assignment atom atomMember green cell
    · have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      exact matchingOfAssignment_covers_clause_green
        source assignment cell clauseIndex clause clauseLookup
        (sourceSatisfies cell clause
          (List.getElem_mem indexLt))
  · intro element elementMember cell
    change element ∈ blueElements source at elementMember
    simp only [blueElements, List.mem_append,
      List.mem_map] at elementMember
    rcases elementMember with
      (⟨clauseIndex, indexMember, rfl⟩ |
        ⟨tagged, taggedMember, rfl⟩) |
        ⟨unusedEntry, unusedMember, rfl⟩
    · have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      exact matchingOfAssignment_covers_clause_blue
        source occurrences assignment cell clauseIndex clause
        clauseLookup
        (sourceSatisfies cell clause
          (List.getElem_mem indexLt))
    · rcases
        exists_occurrenceSlot source occurrences tagged
          taggedMember with ⟨slot, lookup⟩
      exact matchingOfAssignment_covers_complement_blue
        source assignment cell tagged taggedMember slot lookup
    · rcases unusedEntry with ⟨atom, slot⟩
      unfold unusedSlots at unusedMember
      simp only [List.mem_flatMap] at unusedMember
      rcases unusedMember with
        ⟨currentAtom, atomMember, slotMember⟩
      simp only [List.mem_filterMap] at slotMember
      rcases slotMember with
        ⟨currentSlot, currentSlotMember, output⟩
      cases lookup : occurrenceAt source currentAtom currentSlot with
      | some tagged => simp [lookup] at output
      | none =>
          simp [lookup] at output
          rcases output with ⟨rfl, rfl⟩
          exact matchingOfAssignment_covers_unused_blue
            source assignment currentAtom atomMember
              currentSlot lookup cell

/-- Satisfiability of the source exact-one instance implies satisfiability of
the typed periodic 3DM instance. -/
theorem problem_satisfiable_of_source_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (sourceSatisfiable :
      PeriodicOneInThree.Satisfiable source) :
    (problem source).Satisfiable := by
  rcases sourceSatisfiable with ⟨assignment, satisfies⟩
  exact
    ⟨matchingOfAssignment source assignment,
      matchingOfAssignment_satisfies
        source occurrences assignment satisfies⟩

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
