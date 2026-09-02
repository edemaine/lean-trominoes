/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalElementDegreeListSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMDegree

/-! # Structural degree pattern of the typed horizontal 3DM source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

/-- Common degree block contributed in every color by one used variable
occurrence. -/
def horizontalTypedVariableElementDegreeBlock
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) : List Nat :=
  match occurrenceConnectorKind source atom slot with
  | .fixedRed => [2, 2, 2]
  | .fixedGreen | .fixedBlue => [2]

/-- Variable-element degree prefix in variable-major, used-slot-major order. -/
def horizontalTypedVariableElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  (occurringVariables source).flatMap fun atom =>
    (usedSlots source atom).flatMap fun slot =>
      horizontalTypedVariableElementDegreeBlock source atom slot

/-- Common degree block contributed in every color by one clause. -/
def horizontalTypedClauseElementDegreeBlock
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat) : List Nat :=
  if (source.clauses.getD clauseIndex []).length = 3 then
    [3, 3, 3, 3]
  else
    [3, 3, 3, 2]

/-- Clause-element degree suffix in clause presentation order. -/
def horizontalTypedClauseElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  (List.range source.clauses.length).flatMap
    (horizontalTypedClauseElementDegreeBlock source)

/-- The common one-color structural degree pattern. -/
def horizontalTypedOneColorElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  horizontalTypedVariableElementDegrees source ++
    horizontalTypedClauseElementDegrees source

private theorem redOccurrenceElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    (occurrenceRedElements source atom slot).map (fun element =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
          element).length) =
      horizontalTypedVariableElementDegreeBlock source atom slot := by
  cases kindEq : occurrenceConnectorKind source atom slot with
  | fixedRed =>
      simp [occurrenceRedElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        problem_redIncidences_cycleLink_length
          source atom atomMember slot slotMember,
        (fixedRedPrivate_degrees
          source atom atomMember slot slotMember kindEq).1]
  | fixedGreen =>
      simp [occurrenceRedElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        problem_redIncidences_cycleLink_length
          source atom atomMember slot slotMember]
  | fixedBlue =>
      simp [occurrenceRedElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        problem_redIncidences_cycleLink_length
          source atom atomMember slot slotMember]

private theorem greenOccurrenceElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    (occurrenceGreenElements source atom slot).map (fun element =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
          element).length) =
      horizontalTypedVariableElementDegreeBlock source atom slot := by
  cases kindEq : occurrenceConnectorKind source atom slot with
  | fixedRed =>
      simp [occurrenceGreenElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        (fixedRedPrivate_degrees
          source atom atomMember slot slotMember kindEq).2.1]
  | fixedGreen =>
      have degree := (ordinaryPrivate_degrees
        source atom atomMember slot slotMember .fixedGreen kindEq).1
      simpa [occurrenceGreenElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        ordinaryGreenPrivate] using degree
  | fixedBlue =>
      have degree := (ordinaryPrivate_degrees
        source atom atomMember slot slotMember .fixedBlue kindEq).1
      simpa [occurrenceGreenElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        ordinaryGreenPrivate] using degree

private theorem blueOccurrenceElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (slotMember : slot ∈ usedSlots source atom) :
    (occurrenceBlueElements source atom slot).map (fun element =>
        ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
          element).length) =
      horizontalTypedVariableElementDegreeBlock source atom slot := by
  cases kindEq : occurrenceConnectorKind source atom slot with
  | fixedRed =>
      simp [occurrenceBlueElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        (fixedRedPrivate_degrees
          source atom atomMember slot slotMember kindEq).2.2]
  | fixedGreen =>
      have degree := (ordinaryPrivate_degrees
        source atom atomMember slot slotMember .fixedGreen kindEq).2
      simpa [occurrenceBlueElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        ordinaryBluePrivate] using degree
  | fixedBlue =>
      have degree := (ordinaryPrivate_degrees
        source atom atomMember slot slotMember .fixedBlue kindEq).2
      simpa [occurrenceBlueElements,
        horizontalTypedVariableElementDegreeBlock, kindEq,
        ordinaryBluePrivate] using degree

private theorem redClauseElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length) :
    (([RedElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (RedElement.clauseTerminal clauseIndex)).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
        element).length) =
      horizontalTypedClauseElementDegreeBlock source clauseIndex := by
  let clause := source.clauses[clauseIndex]'indexLt
  have clauseLookup : source.clauses[clauseIndex]? = some clause :=
    List.getElem?_eq_getElem indexLt
  have clauseArity := arity clause (List.getElem_mem indexLt)
  have clauseGetD : source.clauses.getD clauseIndex [] = clause :=
    List.getD_eq_getElem _ _ indexLt
  have terminalDegree (group : PlanarThreeDM.X3CClauseTerminalGroup) :
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
        (.clauseTerminal clauseIndex group)).length =
        if clause.length = 2 ∧ group = .right then 2 else 3 := by
    rw [problem_redIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
      terminalOccurrenceEnumeration_length_of_arity
        source occurrences clauseIndex clause clauseLookup clauseArity group]
    by_cases special : clause.length = 2 ∧ group = .right <;>
      simp [special]
  unfold horizontalTypedClauseElementDegreeBlock
  rw [clauseGetD]
  rcases clauseArity with lengthTwo | lengthThree
  · simp [lengthTwo, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).1,
      terminalDegree]
  · simp [lengthThree, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).1,
      terminalDegree]

private theorem greenClauseElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length) :
    (([GreenElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (GreenElement.clauseTerminal clauseIndex)).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
        element).length) =
      horizontalTypedClauseElementDegreeBlock source clauseIndex := by
  let clause := source.clauses[clauseIndex]'indexLt
  have clauseLookup : source.clauses[clauseIndex]? = some clause :=
    List.getElem?_eq_getElem indexLt
  have clauseArity := arity clause (List.getElem_mem indexLt)
  have clauseGetD : source.clauses.getD clauseIndex [] = clause :=
    List.getD_eq_getElem _ _ indexLt
  have terminalDegree (group : PlanarThreeDM.X3CClauseTerminalGroup) :
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
        (.clauseTerminal clauseIndex group)).length =
        if clause.length = 2 ∧ group = .right then 2 else 3 := by
    rw [problem_greenIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
      terminalOccurrenceEnumeration_length_of_arity
        source occurrences clauseIndex clause clauseLookup clauseArity group]
    by_cases special : clause.length = 2 ∧ group = .right <;>
      simp [special]
  unfold horizontalTypedClauseElementDegreeBlock
  rw [clauseGetD]
  rcases clauseArity with lengthTwo | lengthThree
  · simp [lengthTwo, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).2.1,
      terminalDegree]
  · simp [lengthThree, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).2.1,
      terminalDegree]

private theorem blueClauseElementDegrees
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length) :
    (([BlueElement.clauseInternal clauseIndex] ++
        allTerminalGroups.map
          (BlueElement.clauseTerminal clauseIndex)).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
        element).length) =
      horizontalTypedClauseElementDegreeBlock source clauseIndex := by
  let clause := source.clauses[clauseIndex]'indexLt
  have clauseLookup : source.clauses[clauseIndex]? = some clause :=
    List.getElem?_eq_getElem indexLt
  have clauseArity := arity clause (List.getElem_mem indexLt)
  have clauseGetD : source.clauses.getD clauseIndex [] = clause :=
    List.getD_eq_getElem _ _ indexLt
  have terminalDegree (group : PlanarThreeDM.X3CClauseTerminalGroup) :
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
        (.clauseTerminal clauseIndex group)).length =
        if clause.length = 2 ∧ group = .right then 2 else 3 := by
    rw [problem_blueIncidences_clauseTerminal_length
      source clauseIndex indexLt group,
      terminalOccurrenceEnumeration_length_of_arity
        source occurrences clauseIndex clause clauseLookup clauseArity group]
    by_cases special : clause.length = 2 ∧ group = .right <;>
      simp [special]
  unfold horizontalTypedClauseElementDegreeBlock
  rw [clauseGetD]
  rcases clauseArity with lengthTwo | lengthThree
  · simp [lengthTwo, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).2.2,
      terminalDegree]
  · simp [lengthThree, allTerminalGroups,
      (clauseInternal_degrees source clauseIndex indexLt).2.2,
      terminalDegree]

/-- The red presentation realizes the common one-color structural degree
pattern. -/
theorem redElementDegrees_eq_horizontalTypedOneColor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    ((redElements source).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).redIncidences
        element).length) =
      horizontalTypedOneColorElementDegrees source := by
  unfold redElements horizontalTypedOneColorElementDegrees
  rw [List.map_append]
  apply congrArg₂ (· ++ ·)
  · unfold horizontalTypedVariableElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom atomMember
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro slot slotMember
    exact redOccurrenceElementDegrees
      source atom atomMember slot slotMember
  · unfold horizontalTypedClauseElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro clauseIndex indexMember
    exact redClauseElementDegrees source occurrences arity clauseIndex
      (List.mem_range.mp indexMember)

/-- The green presentation realizes the common one-color structural degree
pattern. -/
theorem greenElementDegrees_eq_horizontalTypedOneColor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    ((greenElements source).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).greenIncidences
        element).length) =
      horizontalTypedOneColorElementDegrees source := by
  unfold greenElements horizontalTypedOneColorElementDegrees
  rw [List.map_append]
  apply congrArg₂ (· ++ ·)
  · unfold horizontalTypedVariableElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom atomMember
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro slot slotMember
    exact greenOccurrenceElementDegrees
      source atom atomMember slot slotMember
  · unfold horizontalTypedClauseElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro clauseIndex indexMember
    exact greenClauseElementDegrees source occurrences arity clauseIndex
      (List.mem_range.mp indexMember)

/-- The blue presentation realizes the common one-color structural degree
pattern. -/
theorem blueElementDegrees_eq_horizontalTypedOneColor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    ((blueElements source).map fun element =>
      ((PeriodicPlanarOneInThreeToThreeDM.problem source).blueIncidences
        element).length) =
      horizontalTypedOneColorElementDegrees source := by
  unfold blueElements horizontalTypedOneColorElementDegrees
  rw [List.map_append]
  apply congrArg₂ (· ++ ·)
  · unfold horizontalTypedVariableElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro atom atomMember
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro slot slotMember
    exact blueOccurrenceElementDegrees
      source atom atomMember slot slotMember
  · unfold horizontalTypedClauseElementDegrees
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro clauseIndex indexMember
    exact blueClauseElementDegrees source occurrences arity clauseIndex
      (List.mem_range.mp indexMember)

/-- Under the source promises, the full color-major degree column consists of
three copies of one common structural pattern. -/
theorem horizontalTypedElementDegrees_eq_threeCopies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (occurrences : source.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source) :
    horizontalTypedElementDegrees source =
      horizontalTypedOneColorElementDegrees source ++
      horizontalTypedOneColorElementDegrees source ++
      horizontalTypedOneColorElementDegrees source := by
  unfold horizontalTypedElementDegrees
  rw [redElementDegrees_eq_horizontalTypedOneColor source occurrences arity,
    greenElementDegrees_eq_horizontalTypedOneColor source occurrences arity,
    blueElementDegrees_eq_horizontalTypedOneColor source occurrences arity]

end LeanTrominoes.PeriodicCNFStripReduction

end
