import LeanTrominoes.PeriodicOneInThreeToThreeDMTypedCompleteness

/-!
# Soundness of the typed periodic 3DM reduction

An arbitrary perfect matching covers the internal red and green elements of
every variable six-cycle, so the verified gadget classification recovers one
Boolean value at every variable cell.  Each main clause-blue incidence then
reads the corresponding recovered literal truth value.  Its exact-cover
constraint therefore recovers every source exact-one clause.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Typed exact cover forces the six-cycle predicate at every listed variable
and translated cell. -/
theorem variableGadgetHolds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (cell : Cell) :
    PlanarThreeDM.VariableGadgetHolds fun triple =>
      matching (.variable atom triple) cell := by
  apply variableGadgetHolds_of_internal_covers
    source matching atom atomMember cell
  · intro red
    exact satisfies.1 (.variable atom red)
      (by
        change RedElement.variable atom red ∈ redElements source
        exact variableRed_mem source atom atomMember red)
      cell
  · intro green
    exact satisfies.2.1 (.variable atom green)
      (by
        change GreenElement.variable atom green ∈ greenElements source
        exact variableGreen_mem source atom atomMember green)
      cell

/-- At one variable slot, an arbitrary perfect matching's retained main-blue
incidence reads exactly the recovered source literal truth value. -/
theorem matching_mainClauseIncidenceAt_values_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (translate : Cell) (atom : Variable)
    (slot : OccurrenceSlot) (clauseIndex : Nat) :
    (mainClauseIncidenceAt source atom slot clauseIndex).map
        (fun incidence =>
          (problem source).incidenceValue
            matching incidence translate) =
      (mainClauseOccurrenceOption source clauseIndex
        (atom, slot)).toList.map fun tagged =>
          PeriodicOneInThree.literalTruth
            (assignmentOfMatching matching) translate tagged.1 := by
  cases lookup : occurrenceAt source atom slot with
  | none =>
      simp [mainClauseIncidenceAt, mainClauseOccurrenceOption,
        lookup]
  | some tagged =>
      by_cases sameClause : tagged.2.1 = clauseIndex
      · have taggedData :=
          occurrenceAt_mem_and_atom
            source atom slot tagged lookup
        have atomMember :=
          atom_mem_occurringVariables_of_tagged_mem
            source tagged taggedData.1
        have atomEq : atom = tagged.1.atom :=
          taggedData.2.symm
        subst atom
        simp only [mainClauseIncidenceAt,
          mainClauseOccurrenceOption, lookup, sameClause,
          if_true, List.map_cons, List.map_nil,
          Option.toList_some]
        simp only [TypedPeriodicThreeDM.incidenceValue,
          sub_reverseOffset]
        exact congrArg (fun value => [value])
          (matching_literalPort_eq_literalTruth
            matching translate tagged.1 slot
            (variableGadgetHolds_of_satisfies
              source matching satisfies tagged.1.atom
                atomMember
                (Cell.add translate tagged.1.offset)))
      · simp [mainClauseIncidenceAt, mainClauseOccurrenceOption,
          lookup, sameClause]

/-- Main clause-blue values of an arbitrary perfect matching equal the
variable/slot occurrence enumeration mapped through the recovered Boolean
assignment. -/
theorem matching_blueIncidentValues_clause_eq_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (translate : Cell) (clauseIndex : Nat) :
    (problem source).blueIncidentValues
        matching (.clause clauseIndex) translate =
      (mainClauseOccurrenceEnumeration source clauseIndex).map
        fun tagged =>
          PeriodicOneInThree.literalTruth
            (assignmentOfMatching matching) translate tagged.1 := by
  rw [TypedPeriodicThreeDM.blueIncidentValues,
    problem_blueIncidences_clause]
  unfold mainClauseIncidences mainClauseIncidencesForAtom
  simp only [List.map_flatMap]
  simp_rw [matching_mainClauseIncidenceAt_values_of_satisfies
    source matching satisfies translate]
  exact
    (map_filterMap_product
      (occurringVariables source) OccurrenceSlot.all
      (mainClauseOccurrenceOption source clauseIndex)
      (fun tagged =>
        PeriodicOneInThree.literalTruth
          (assignmentOfMatching matching)
          translate tagged.1)).symm

/-- Under the occurrence-three bound, arbitrary matching values at a valid
main clause-blue element are a permutation of the recovered source clause
values. -/
theorem matching_blueIncidentValues_clause_perm_clauseValues_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    List.Perm
      ((problem source).blueIncidentValues
        matching (.clause clauseIndex) translate)
      (PeriodicOneInThree.clauseValues
        (assignmentOfMatching matching) translate clause) := by
  rw [matching_blueIncidentValues_clause_eq_of_satisfies
    source matching satisfies translate clauseIndex]
  exact
    ((mainClauseOccurrenceEnumeration_perm_clauseOccurrences
      source occurrences clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          (assignmentOfMatching matching)
          translate tagged.1).trans
      (clauseOccurrences_values_perm_clauseValues
        source (assignmentOfMatching matching) translate
          clauseIndex clause clauseLookup)

/-- Every perfect matching of the typed construction yields a satisfying
assignment of the source exact-one instance. -/
theorem assignmentOfMatching_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (matching : (problem source).MatchingAssignment)
    (matchingSatisfies : (problem source).Satisfies matching) :
    PeriodicOneInThree.Satisfies source
      (assignmentOfMatching matching) := by
  intro translate clause clauseMember
  rcases List.mem_iff_getElem?.mp clauseMember with
    ⟨clauseIndex, clauseLookup⟩
  have indexLt :=
    (List.getElem?_eq_some_iff.mp clauseLookup).1
  have mainCovered :=
    matchingSatisfies.2.2 (.clause clauseIndex)
      (by
        change BlueElement.clause clauseIndex ∈ blueElements source
        exact clauseBlue_mem source clauseIndex indexLt)
      translate
  exact
    (exactlyOne_iff_of_perm
      (matching_blueIncidentValues_clause_perm_clauseValues_of_satisfies
        source occurrences matching matchingSatisfies
          translate clauseIndex clause clauseLookup)).mp
      mainCovered

/-- Typed periodic 3DM satisfiability implies source exact-one
satisfiability. -/
theorem source_satisfiable_of_problem_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (problemSatisfiable : (problem source).Satisfiable) :
    PeriodicOneInThree.Satisfiable source := by
  rcases problemSatisfiable with ⟨matching, satisfies⟩
  exact
    ⟨assignmentOfMatching matching,
      assignmentOfMatching_satisfies
        source occurrences matching satisfies⟩

/-- The typed periodic 3DM construction is satisfiable exactly when its
occurrence-three exact-one source is satisfiable. -/
theorem problem_satisfiable_iff
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3) :
    (problem source).Satisfiable ↔
      PeriodicOneInThree.Satisfiable source := by
  constructor
  · exact source_satisfiable_of_problem_satisfiable
      source occurrences
  · exact problem_satisfiable_of_source_satisfiable
      source occurrences

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
