import LeanTrominoes.PeriodicOneInThreeToThreeDMTypedSoundness

/-!
# Degree bounds for the typed periodic 3DM construction

Variable-internal elements and unused caps have degree two.  Genuine
complement elements have one variable port and one auxiliary.  Clause cores
and main clause-blue elements have the source clause arity, hence degree two
or three for the unit-free exact-one instances used by the reduction.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeToThreeDM

/-- A valid filtered clause-occurrence list has the source clause length. -/
theorem clauseOccurrences_length {Variable : Type*}
    (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    (clauseOccurrences source clauseIndex).length = clause.length := by
  calc
    (clauseOccurrences source clauseIndex).length =
        (taggedClauseOccurrences clauseIndex clause).length :=
      (clauseOccurrences_perm_taggedClauseOccurrences
        source clauseIndex clause clauseLookup).length_eq
    _ = clause.length := by
      simp [taggedClauseOccurrences]

/-- Red clause-core degree is the source clause arity. -/
theorem problem_redIncidences_clause_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    ((problem source).redIncidences
      (.clause clauseIndex)).length = clause.length := by
  rw [problem_redIncidences_clause]
  simp [clauseAuxiliaryIncidences,
    clauseOccurrences_length
      source clauseIndex clause clauseLookup]

/-- Green clause-core degree is the source clause arity. -/
theorem problem_greenIncidences_clause_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    ((problem source).greenIncidences
      (.clause clauseIndex)).length = clause.length := by
  rw [problem_greenIncidences_clause]
  simp [clauseAuxiliaryIncidences,
    clauseOccurrences_length
      source clauseIndex clause clauseLookup]

/-- Main clause-blue degree is likewise the source clause arity under the
occurrence-three bound. -/
theorem problem_blueIncidences_clause_length {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause) :
    ((problem source).blueIncidences
      (.clause clauseIndex)).length = clause.length := by
  have valuesEq :=
    matchingOfAssignment_blueIncidentValues_clause_eq
      source (fun _ _ => false) (0, 0) clauseIndex
  have incidenceLength :
      ((problem source).blueIncidences
        (.clause clauseIndex)).length =
        (mainClauseOccurrenceEnumeration
          source clauseIndex).length := by
    have := congrArg List.length valuesEq
    simpa [TypedPeriodicThreeDM.blueIncidentValues] using this
  calc
    ((problem source).blueIncidences
        (.clause clauseIndex)).length =
        (mainClauseOccurrenceEnumeration
          source clauseIndex).length :=
      incidenceLength
    _ = (clauseOccurrences source clauseIndex).length :=
      (mainClauseOccurrenceEnumeration_perm_clauseOccurrences
        source occurrences clauseIndex).length_eq
    _ = clause.length :=
      clauseOccurrences_length
        source clauseIndex clause clauseLookup

/-- Every declared colored element in the typed construction has degree two
or three. -/
theorem problem_degreeTwoOrThree {Variable : Type*}
    [DecidableEq Variable] (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (problem source).DegreeTwoOrThree := by
  refine ⟨?_, ?_, ?_⟩
  · intro element elementMember
    change element ∈ redElements source at elementMember
    simp only [redElements, List.mem_append, List.mem_flatMap,
      List.mem_map] at elementMember
    rcases elementMember with
      ⟨atom, atomMember, red, redMember, rfl⟩ |
        ⟨clauseIndex, indexMember, rfl⟩
    · rw [problem_redIncidences_variable
      source atom atomMember red]
      cases red <;>
        simp [PlanarThreeDM.VariableRed.neighbors]
    · have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      rw [problem_redIncidences_clause_length
        source clauseIndex clause clauseLookup]
      rcases arity clause (List.getElem_mem indexLt) with
        lengthTwo | lengthThree
      · simp [lengthTwo]
      · simp [lengthThree]
  · intro element elementMember
    change element ∈ greenElements source at elementMember
    simp only [greenElements, List.mem_append, List.mem_flatMap,
      List.mem_map] at elementMember
    rcases elementMember with
      ⟨atom, atomMember, green, greenMember, rfl⟩ |
        ⟨clauseIndex, indexMember, rfl⟩
    · rw [problem_greenIncidences_variable
      source atom atomMember green]
      cases green <;>
        simp [PlanarThreeDM.VariableGreen.neighbors]
    · have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      rw [problem_greenIncidences_clause_length
        source clauseIndex clause clauseLookup]
      rcases arity clause (List.getElem_mem indexLt) with
        lengthTwo | lengthThree
      · simp [lengthTwo]
      · simp [lengthThree]
  · intro element elementMember
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
      rw [problem_blueIncidences_clause_length
        source occurrences clauseIndex clause clauseLookup]
      rcases arity clause (List.getElem_mem indexLt) with
        lengthTwo | lengthThree
      · simp [lengthTwo]
      · simp [lengthThree]
    · rcases
        exists_occurrenceSlot source occurrences tagged
          taggedMember with ⟨slot, lookup⟩
      rw [problem_blueIncidences_complement_of_lookup
        source tagged taggedMember slot lookup]
      simp
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
          rw [problem_blueIncidences_unused
            source currentAtom atomMember currentSlot lookup]
          cases currentSlot <;>
            simp [OccurrenceSlot.triples]

end PeriodicOneInThreeToThreeDM
end LeanTrominoes
