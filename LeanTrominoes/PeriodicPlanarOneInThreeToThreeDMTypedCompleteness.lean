import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMCycleLinkCovers

/-!
# Completeness of the typed planar 3DM assembly

Every satisfying occurrence-three exact-one assignment induces the
canonical perfect matching of the assembled Dyer--Frieze gadgets.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

theorem matchingOfAssignment_covers_ordinary_green
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).greenIncidentValues
        (matchingOfAssignment source assignment)
        (.ordinaryInternal atom slot
          (ordinaryGreenPrivate variant)) cell) := by
  rw [TypedProblem.greenIncidentValues,
    problem_greenIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq]
  have holds :=
    matchingOfAssignment_ordinary_holds
      source assignment atom slot variant cell
  cases variant with
  | fixedGreen =>
      simpa [ordinaryGreenPrivate, ordinaryGreenPrivateNeighbors,
        VariableOccurrenceElement.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2
  | fixedBlue =>
      simpa [ordinaryGreenPrivate, ordinaryGreenPrivateNeighbors,
        VariableOccurrenceElement.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.1

theorem matchingOfAssignment_covers_ordinary_blue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue)
    (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.ordinaryInternal atom slot
          (ordinaryBluePrivate variant)) cell) := by
  rw [TypedProblem.blueIncidentValues,
    problem_blueIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq]
  have holds :=
    matchingOfAssignment_ordinary_holds
      source assignment atom slot variant cell
  cases variant with
  | fixedGreen =>
      simpa [ordinaryBluePrivate, ordinaryBluePrivateNeighbors,
        VariableOccurrenceElement.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.1
  | fixedBlue =>
      simpa [ordinaryBluePrivate, ordinaryBluePrivateNeighbors,
        VariableOccurrenceElement.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2

theorem matchingOfAssignment_covers_fixedRed_red
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalRed) (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).redIncidentValues
        (matchingOfAssignment source assignment)
        (.fixedRedInternal atom slot element) cell) := by
  rw [TypedProblem.redIncidentValues,
    problem_redIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
  have holds :=
    matchingOfAssignment_fixedRed_holds
      source assignment atom slot cell
  cases element with
  | middleRung =>
      simpa [fixedRedPhysicalRed,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.1
  | topAuxiliary =>
      simpa [fixedRedPhysicalRed,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.1

theorem matchingOfAssignment_covers_fixedRed_green
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalGreen) (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).greenIncidentValues
        (matchingOfAssignment source assignment)
        (.fixedRedInternal atom slot element) cell) := by
  rw [TypedProblem.greenIncidentValues,
    problem_greenIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
  have holds :=
    matchingOfAssignment_fixedRed_holds
      source assignment atom slot cell
  cases element with
  | leftRung =>
      simpa [fixedRedPhysicalGreen,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.1
  | topRightLink =>
      simpa [fixedRedPhysicalGreen,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.2.1
  | bottomRightLink =>
      simpa [fixedRedPhysicalGreen,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.2.2.1

theorem matchingOfAssignment_covers_fixedRed_blue
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (element : FixedRedInternalBlue) (cell : Cell) :
    PeriodicOneInThree.ExactlyOne
      ((problem source).blueIncidentValues
        (matchingOfAssignment source assignment)
        (.fixedRedInternal atom slot element) cell) := by
  rw [TypedProblem.blueIncidentValues,
    problem_blueIncidences_fixedRedInternal
      source atom atomMember slot slotMember kindEq element]
  have holds :=
    matchingOfAssignment_fixedRed_holds
      source assignment atom slot cell
  cases element with
  | topLeftLink =>
      simpa [fixedRedPhysicalBlue,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.2.2.2.1
  | bottomLeftLink =>
      simpa [fixedRedPhysicalBlue,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.2.2.2.2.1
  | rightRung =>
      simpa [fixedRedPhysicalBlue,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using holds.2.2.2.2.2.2.2

theorem matchingOfAssignment_covers_clauseInternal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (assignment : Variable → Cell → Bool)
    (cell : Cell) (clauseIndex : Nat)
    (clause : PeriodicClause Variable)
    (clauseLookup : source.clauses[clauseIndex]? = some clause)
    (arity : clause.length = 2 ∨ clause.length = 3)
    (sourceHolds :
      PeriodicOneInThree.ClauseHolds assignment cell clause) :
    PeriodicOneInThree.ExactlyOne
        ((problem source).redIncidentValues
          (matchingOfAssignment source assignment)
          (.clauseInternal clauseIndex) cell) ∧
      PeriodicOneInThree.ExactlyOne
        ((problem source).greenIncidentValues
          (matchingOfAssignment source assignment)
          (.clauseInternal clauseIndex) cell) ∧
      PeriodicOneInThree.ExactlyOne
        ((problem source).blueIncidentValues
          (matchingOfAssignment source assignment)
          (.clauseInternal clauseIndex) cell) := by
  have indexLt := (List.getElem?_eq_some_iff.mp clauseLookup).1
  have coreHolds :=
    matchingOfAssignment_clause_holds
      source assignment cell clauseIndex
      (sourceTerminalSignals_exactlyOne source assignment cell
        clauseIndex clause clauseLookup arity sourceHolds)
  constructor
  · rw [TypedProblem.redIncidentValues,
      problem_redIncidences_clauseInternal
        source clauseIndex indexLt]
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using coreHolds.1 .left
  constructor
  · rw [TypedProblem.greenIncidentValues,
      problem_greenIncidences_clauseInternal
        source clauseIndex indexLt]
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using coreHolds.1 .right
  · rw [TypedProblem.blueIncidentValues,
      problem_blueIncidences_clauseInternal
        source clauseIndex indexLt]
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using coreHolds.1 .bottom

/-- Every satisfying source assignment induces a perfect matching of the
typed planar 3DM assembly. -/
theorem matchingOfAssignment_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (assignment : Variable → Cell → Bool)
    (sourceSatisfies :
      PeriodicOneInThree.Satisfies source assignment) :
    (problem source).Satisfies
      (matchingOfAssignment source assignment) := by
  refine ⟨?_, ?_, ?_⟩
  · intro element elementMember cell
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
          · exact matchingOfAssignment_covers_cycleLink
              source assignment atom atomMember slot slotMember cell
          · exact matchingOfAssignment_covers_fixedRed_red
              source assignment atom atomMember slot slotMember
                kindEq .middleRung cell
          · exact matchingOfAssignment_covers_fixedRed_red
              source assignment atom atomMember slot slotMember
                kindEq .topAuxiliary cell
      | fixedGreen =>
          simp [occurrenceRedElements, kindEq] at localMember
          subst element
          exact matchingOfAssignment_covers_cycleLink
            source assignment atom atomMember slot slotMember cell
      | fixedBlue =>
          simp [occurrenceRedElements, kindEq] at localMember
          subst element
          exact matchingOfAssignment_covers_cycleLink
            source assignment atom atomMember slot slotMember cell
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      have clauseArity := arity clause (List.getElem_mem indexLt)
      have clauseHolds :=
        sourceSatisfies cell clause (List.getElem_mem indexLt)
      simp only [List.mem_singleton, List.mem_map] at localMember
      rcases localMember with rfl | ⟨group, groupMember, rfl⟩
      · exact (matchingOfAssignment_covers_clauseInternal
          source assignment cell clauseIndex clause clauseLookup
            clauseArity clauseHolds).1
      · simpa [TypedProblem.redIncidentValues,
          problemTerminalIncidences] using
            matchingOfAssignment_covers_terminal
              source occurrences assignment cell clauseIndex clause
                clauseLookup clauseArity clauseHolds .red group
  · intro element elementMember cell
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
          · exact matchingOfAssignment_covers_fixedRed_green
              source assignment atom atomMember slot slotMember
                kindEq .leftRung cell
          · exact matchingOfAssignment_covers_fixedRed_green
              source assignment atom atomMember slot slotMember
                kindEq .topRightLink cell
          · exact matchingOfAssignment_covers_fixedRed_green
              source assignment atom atomMember slot slotMember
                kindEq .bottomRightLink cell
      | fixedGreen =>
          simp [occurrenceGreenElements, kindEq] at localMember
          subst element
          simpa [ordinaryGreenPrivate] using
            matchingOfAssignment_covers_ordinary_green
              source assignment atom atomMember slot slotMember
                .fixedGreen kindEq cell
      | fixedBlue =>
          simp [occurrenceGreenElements, kindEq] at localMember
          subst element
          simpa [ordinaryGreenPrivate] using
            matchingOfAssignment_covers_ordinary_green
              source assignment atom atomMember slot slotMember
                .fixedBlue kindEq cell
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      have clauseArity := arity clause (List.getElem_mem indexLt)
      have clauseHolds :=
        sourceSatisfies cell clause (List.getElem_mem indexLt)
      simp only [List.mem_singleton, List.mem_map] at localMember
      rcases localMember with rfl | ⟨group, groupMember, rfl⟩
      · exact (matchingOfAssignment_covers_clauseInternal
          source assignment cell clauseIndex clause clauseLookup
            clauseArity clauseHolds).2.1
      · simpa [TypedProblem.greenIncidentValues,
          problemTerminalIncidences] using
            matchingOfAssignment_covers_terminal
              source occurrences assignment cell clauseIndex clause
                clauseLookup clauseArity clauseHolds .green group
  · intro element elementMember cell
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
          · exact matchingOfAssignment_covers_fixedRed_blue
              source assignment atom atomMember slot slotMember
                kindEq .topLeftLink cell
          · exact matchingOfAssignment_covers_fixedRed_blue
              source assignment atom atomMember slot slotMember
                kindEq .bottomLeftLink cell
          · exact matchingOfAssignment_covers_fixedRed_blue
              source assignment atom atomMember slot slotMember
                kindEq .rightRung cell
      | fixedGreen =>
          simp [occurrenceBlueElements, kindEq] at localMember
          subst element
          simpa [ordinaryBluePrivate] using
            matchingOfAssignment_covers_ordinary_blue
              source assignment atom atomMember slot slotMember
                .fixedGreen kindEq cell
      | fixedBlue =>
          simp [occurrenceBlueElements, kindEq] at localMember
          subst element
          simpa [ordinaryBluePrivate] using
            matchingOfAssignment_covers_ordinary_blue
              source assignment atom atomMember slot slotMember
                .fixedBlue kindEq cell
    · rcases clauseMember with
        ⟨clauseIndex, indexMember, localMember⟩
      have indexLt := List.mem_range.mp indexMember
      let clause := source.clauses[clauseIndex]'indexLt
      have clauseLookup :
          source.clauses[clauseIndex]? = some clause :=
        List.getElem?_eq_getElem indexLt
      have clauseArity := arity clause (List.getElem_mem indexLt)
      have clauseHolds :=
        sourceSatisfies cell clause (List.getElem_mem indexLt)
      simp only [List.mem_singleton, List.mem_map] at localMember
      rcases localMember with rfl | ⟨group, groupMember, rfl⟩
      · exact (matchingOfAssignment_covers_clauseInternal
          source assignment cell clauseIndex clause clauseLookup
            clauseArity clauseHolds).2.2
      · simpa [TypedProblem.blueIncidentValues,
          problemTerminalIncidences] using
            matchingOfAssignment_covers_terminal
              source occurrences assignment cell clauseIndex clause
                clauseLookup clauseArity clauseHolds .blue group

/-- Typed satisfiability follows from source satisfiability. -/
theorem problem_satisfiable_of_source_satisfiable
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (sourceSatisfiable : PeriodicOneInThree.Satisfiable source) :
    (problem source).Satisfiable := by
  rcases sourceSatisfiable with ⟨assignment, satisfies⟩
  exact ⟨matchingOfAssignment source assignment,
    matchingOfAssignment_satisfies
      source occurrences arity assignment satisfies⟩

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
