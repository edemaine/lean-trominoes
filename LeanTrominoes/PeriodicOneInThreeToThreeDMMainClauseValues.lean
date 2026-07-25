import LeanTrominoes.PeriodicOneInThreeToThreeDMClauseOccurrenceValues

/-!
# Canonical values at main clause-blue elements

For the matching induced by a source Boolean assignment, each retained main
clause incidence reads exactly the corresponding source literal truth value.
The actual incidence-value list is therefore the variable/slot occurrence
enumeration mapped to truth values, and hence is a permutation of the source
clause values.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- Mapping a `filterMap` over a list product can be presented as the
corresponding nested `flatMap`. -/
theorem map_filterMap_product {First Second Output Value : Type*}
    (first : List First) (second : List Second)
    (filter : First × Second → Option Output)
    (value : Output → Value) :
    ((first ×ˢ second).filterMap filter).map value =
      first.flatMap fun left =>
        second.flatMap fun right =>
          (filter (left, right)).toList.map value := by
  induction first with
  | nil => rfl
  | cons head tail induction =>
      simp [List.filterMap_eq_flatMap_toList,
        List.map_flatMap]
      rw [List.flatMap_map]
      rw [← induction]
      rw [List.filterMap_eq_flatMap_toList,
        List.map_flatMap]

/-- The canonical values contributed by one variable slot agree with the
optional tagged occurrence recorded for that slot and clause. -/
theorem matchingOfAssignment_mainClauseIncidenceAt_values
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (atom : Variable)
    (slot : OccurrenceSlot) (clauseIndex : Nat) :
    (mainClauseIncidenceAt source atom slot clauseIndex).map
        (fun incidence =>
          (problem source).incidenceValue
            (matchingOfAssignment source assignment)
            incidence translate) =
      (mainClauseOccurrenceOption source clauseIndex
        (atom, slot)).toList.map fun tagged =>
          PeriodicOneInThree.literalTruth
            assignment translate tagged.1 := by
  cases lookup : occurrenceAt source atom slot with
  | none =>
      simp [mainClauseIncidenceAt, mainClauseOccurrenceOption,
        lookup]
  | some tagged =>
      by_cases sameClause : tagged.2.1 = clauseIndex
      · simp [mainClauseIncidenceAt, mainClauseOccurrenceOption,
          lookup, sameClause,
          matchingOfAssignment_literalIncidence
            source assignment translate atom slot tagged lookup]
      · simp [mainClauseIncidenceAt, mainClauseOccurrenceOption,
          lookup, sameClause]

/-- The actual canonical incident-value list at a main clause-blue element is
the variable/slot occurrence enumeration mapped to source literal truths. -/
theorem matchingOfAssignment_blueIncidentValues_clause_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat) :
    (problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate =
      (mainClauseOccurrenceEnumeration source clauseIndex).map
        fun tagged =>
          PeriodicOneInThree.literalTruth
            assignment translate tagged.1 := by
  rw [TypedPeriodicThreeDM.blueIncidentValues,
    problem_blueIncidences_clause]
  unfold mainClauseIncidences mainClauseIncidencesForAtom
  simp only [List.map_flatMap]
  simp_rw [matchingOfAssignment_mainClauseIncidenceAt_values
    source assignment translate]
  exact
    (map_filterMap_product
      (occurringVariables source) OccurrenceSlot.all
      (mainClauseOccurrenceOption source clauseIndex)
      (fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1)).symm

/-- Under the occurrence-three bound, canonical main-blue values are a
permutation of the source-order tagged literal truth values. -/
theorem matchingOfAssignment_blueIncidentValues_clause_perm_occurrences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat) :
    List.Perm
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate)
      ((clauseOccurrences source clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1) := by
  rw [matchingOfAssignment_blueIncidentValues_clause_eq]
  exact
    (mainClauseOccurrenceEnumeration_perm_clauseOccurrences
      source occurrences clauseIndex).map fun tagged =>
        PeriodicOneInThree.literalTruth
          assignment translate tagged.1

/-- At a valid clause index, canonical main-blue values are a permutation of
the ordinary source clause values. -/
theorem matchingOfAssignment_blueIncidentValues_clause_perm_clauseValues
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (assignment : Variable → Cell → Bool)
    (translate : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    List.Perm
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.clause clauseIndex) translate)
      (PeriodicOneInThree.clauseValues
        assignment translate clause) := by
  exact
    (matchingOfAssignment_blueIncidentValues_clause_perm_occurrences
      source occurrences assignment translate clauseIndex).trans
        (clauseOccurrences_values_perm_clauseValues
          source assignment translate clauseIndex clause
          clauseLookup)

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
