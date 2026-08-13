/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseTerminalIncidences

/-!
# Degree bounds for the typed planar periodic 3DM assembly

This file combines the incidence classifications for cycle links, ordinary
and fixed-red private elements, clause internals, and clause terminals.  If
variables occur at most three times and every clause has arity two or three,
every declared colored element has degree two or three.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

theorem redClauseTerminal_degree_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    ((problem source).redIncidences
      (.clauseTerminal clauseIndex group)).length ∈
        ([2, 3] : List Nat) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  rw [problem_redIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
    terminalOccurrenceEnumeration_length_of_arity
      source occurrences clauseIndex clause clauseLookup arity group]
  rcases arity with lengthTwo | lengthThree <;>
    cases group <;> simp_all

theorem greenClauseTerminal_degree_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    ((problem source).greenIncidences
      (.clauseTerminal clauseIndex group)).length ∈
        ([2, 3] : List Nat) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  rw [problem_greenIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
    terminalOccurrenceEnumeration_length_of_arity
      source occurrences clauseIndex clause clauseLookup arity group]
  rcases arity with lengthTwo | lengthThree <;>
    cases group <;> simp_all

theorem blueClauseTerminal_degree_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (clauseIndex : Nat) (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (group : X3CClauseTerminalGroup) :
    ((problem source).blueIncidences
      (.clauseTerminal clauseIndex group)).length ∈
        ([2, 3] : List Nat) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  rw [problem_blueIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
    terminalOccurrenceEnumeration_length_of_arity
      source occurrences clauseIndex clause clauseLookup arity group]
  rcases arity with lengthTwo | lengthThree <;>
    cases group <;> simp_all

/-- Every declared colored element in the typed planar assembly has degree
two or three. -/
theorem problem_degreeTwoOrThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    (problem source).DegreeTwoOrThree := by
  refine ⟨?_, ?_, ?_⟩
  · intro element elementMember
    change element ∈ redElements source at elementMember
    simp only [redElements, List.mem_append,
      List.mem_flatMap] at elementMember
    rcases elementMember with variableMember | clauseMember
    · rcases variableMember with
        ⟨atom, atomMember, slot, slotMember, localMember⟩
      cases kindEq :
          occurrenceConnectorKind source atom slot with
      | fixedRed =>
          simp [occurrenceRedElements, kindEq] at localMember
          rcases localMember with rfl | rfl | rfl
          · simp [problem_redIncidences_cycleLink_length
              source atom atomMember slot slotMember]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).1 .middleRung]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).1 .topAuxiliary]
      | fixedGreen =>
          simp [occurrenceRedElements, kindEq] at localMember
          subst element
          simp [problem_redIncidences_cycleLink_length
            source atom atomMember slot slotMember]
      | fixedBlue =>
          simp [occurrenceRedElements, kindEq] at localMember
          subst element
          simp [problem_redIncidences_cycleLink_length
            source atom atomMember slot slotMember]
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      simp only [List.mem_singleton,
        List.mem_map] at localMember
      rcases localMember with rfl |
          ⟨group, groupMember, rfl⟩
      · simp [(clauseInternal_degrees
          source clauseIndex indexLt).1]
      · exact redClauseTerminal_degree_mem
          source occurrences clauseIndex clause clauseLookup
            (arity clause (List.getElem_mem indexLt)) group
  · intro element elementMember
    change element ∈ greenElements source at elementMember
    simp only [greenElements, List.mem_append,
      List.mem_flatMap] at elementMember
    rcases elementMember with variableMember | clauseMember
    · rcases variableMember with
        ⟨atom, atomMember, slot, slotMember, localMember⟩
      cases kindEq :
          occurrenceConnectorKind source atom slot with
      | fixedRed =>
          simp [occurrenceGreenElements, kindEq] at localMember
          rcases localMember with rfl | rfl | rfl
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .leftRung]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .topRightLink]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.1 .bottomRightLink]
      | fixedGreen =>
          simp [occurrenceGreenElements, kindEq] at localMember
          subst element
          have degreeEq :
              ((problem source).greenIncidences
                (.ordinaryInternal atom slot
                  .cycleShared)).length = 2 := by
            simpa [ordinaryGreenPrivate] using
              (ordinaryPrivate_degrees source atom atomMember
                slot slotMember .fixedGreen kindEq).1
          rw [degreeEq]
          simp
      | fixedBlue =>
          simp [occurrenceGreenElements, kindEq] at localMember
          subst element
          have degreeEq :
              ((problem source).greenIncidences
                (.ordinaryInternal atom slot
                  .cycleShared)).length = 2 := by
            simpa [ordinaryGreenPrivate] using
              (ordinaryPrivate_degrees source atom atomMember
                slot slotMember .fixedBlue kindEq).1
          rw [degreeEq]
          simp
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      simp only [List.mem_singleton,
        List.mem_map] at localMember
      rcases localMember with rfl |
          ⟨group, groupMember, rfl⟩
      · simp [(clauseInternal_degrees
          source clauseIndex indexLt).2.1]
      · exact greenClauseTerminal_degree_mem
          source occurrences clauseIndex clause clauseLookup
            (arity clause (List.getElem_mem indexLt)) group
  · intro element elementMember
    change element ∈ blueElements source at elementMember
    simp only [blueElements, List.mem_append,
      List.mem_flatMap] at elementMember
    rcases elementMember with variableMember | clauseMember
    · rcases variableMember with
        ⟨atom, atomMember, slot, slotMember, localMember⟩
      cases kindEq :
          occurrenceConnectorKind source atom slot with
      | fixedRed =>
          simp [occurrenceBlueElements, kindEq] at localMember
          rcases localMember with rfl | rfl | rfl
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .topLeftLink]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .bottomLeftLink]
          · simp [(fixedRedPrivate_degrees source atom atomMember
              slot slotMember kindEq).2.2 .rightRung]
      | fixedGreen =>
          simp [occurrenceBlueElements, kindEq] at localMember
          subst element
          have degreeEq :
              ((problem source).blueIncidences
                (.ordinaryInternal atom slot
                  .auxiliaryShared)).length = 2 := by
            simpa [ordinaryBluePrivate] using
              (ordinaryPrivate_degrees source atom atomMember
                slot slotMember .fixedGreen kindEq).2
          rw [degreeEq]
          simp
      | fixedBlue =>
          simp [occurrenceBlueElements, kindEq] at localMember
          subst element
          have degreeEq :
              ((problem source).blueIncidences
                (.ordinaryInternal atom slot
                  .auxiliaryShared)).length = 2 := by
            simpa [ordinaryBluePrivate] using
              (ordinaryPrivate_degrees source atom atomMember
                slot slotMember .fixedBlue kindEq).2
          rw [degreeEq]
          simp
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      simp only [List.mem_singleton,
        List.mem_map] at localMember
      rcases localMember with rfl |
          ⟨group, groupMember, rfl⟩
      · simp [(clauseInternal_degrees
          source clauseIndex indexLt).2.2]
      · exact blueClauseTerminal_degree_mem
          source occurrences clauseIndex clause clauseLookup
            (arity clause (List.getElem_mem indexLt)) group

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
