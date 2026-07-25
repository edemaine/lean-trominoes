import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTypedCompleteness

/-!
# Local soundness of the typed planar 3DM assembly

Every perfect matching of the assembled typed instance restricts to a valid
selection of each finite Dyer--Frieze gadget.  This file recovers the private
constraints of the ordinary occurrence modules and fixed-red detours, together
with the three internal constraints of every clause core.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

private theorem ordinaryGreenPrivate_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    GreenElement.ordinaryInternal atom slot
        (ordinaryGreenPrivate variant) ∈
      greenElements source := by
  simp only [greenElements, List.mem_append, List.mem_flatMap]
  left
  refine ⟨atom, atomMember, slot, slotMember, ?_⟩
  cases variant <;>
    simp_all [occurrenceGreenElements, ordinaryGreenPrivate]

private theorem ordinaryBluePrivate_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue) :
    BlueElement.ordinaryInternal atom slot
        (ordinaryBluePrivate variant) ∈
      blueElements source := by
  simp only [blueElements, List.mem_append, List.mem_flatMap]
  left
  refine ⟨atom, atomMember, slot, slotMember, ?_⟩
  cases variant <;>
    simp_all [occurrenceBlueElements, ordinaryBluePrivate]

/-- The restriction of a global perfect matching to an ordinary occurrence
module satisfies both of its private degree-two constraints. -/
theorem ordinary_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (kindEq :
      occurrenceConnectorKind source atom slot =
        match variant with
        | .fixedGreen => .fixedGreen
        | .fixedBlue => .fixedBlue)
    (cell : Cell) :
    VariableOccurrenceHolds fun triple =>
      matching (.ordinary atom slot variant triple) cell := by
  have greenCover :=
    satisfies.2.1
      (.ordinaryInternal atom slot (ordinaryGreenPrivate variant))
      (ordinaryGreenPrivate_mem
        source atom atomMember slot slotMember variant kindEq)
      cell
  have blueCover :=
    satisfies.2.2
      (.ordinaryInternal atom slot (ordinaryBluePrivate variant))
      (ordinaryBluePrivate_mem
        source atom atomMember slot slotMember variant kindEq)
      cell
  rw [TypedProblem.greenIncidentValues,
    problem_greenIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq] at greenCover
  rw [TypedProblem.blueIncidentValues,
    problem_blueIncidences_ordinaryInternal
      source atom atomMember slot slotMember variant kindEq] at blueCover
  cases variant with
  | fixedGreen =>
      constructor
      · simpa [ordinaryBluePrivate, ordinaryBluePrivateNeighbors,
          VariableOccurrenceElement.neighbors,
          TypedProblem.incidenceValue, Cell.sub,
          List.map_map, Function.comp_def] using blueCover
      · simpa [ordinaryGreenPrivate, ordinaryGreenPrivateNeighbors,
          VariableOccurrenceElement.neighbors,
          TypedProblem.incidenceValue, Cell.sub,
          List.map_map, Function.comp_def] using greenCover
  | fixedBlue =>
      constructor
      · simpa [ordinaryGreenPrivate, ordinaryGreenPrivateNeighbors,
          VariableOccurrenceElement.neighbors,
          TypedProblem.incidenceValue, Cell.sub,
          List.map_map, Function.comp_def] using greenCover
      · simpa [ordinaryBluePrivate, ordinaryBluePrivateNeighbors,
          VariableOccurrenceElement.neighbors,
          TypedProblem.incidenceValue, Cell.sub,
          List.map_map, Function.comp_def] using blueCover

/-- The restriction of a global perfect matching to a fixed-red occurrence
module satisfies all eight private degree-two constraints. -/
theorem fixedRed_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (kindEq : occurrenceConnectorKind source atom slot = .fixedRed)
    (cell : Cell) :
    FixedRedConnectorHolds fun triple =>
      matching (.fixedRed atom slot triple) cell := by
  have redCover (element : FixedRedInternalRed) :
      PeriodicOneInThree.ExactlyOne
        (((fixedRedPhysicalRed element).neighbors).map fun triple =>
          matching (.fixedRed atom slot triple) cell) := by
    have cover :=
      satisfies.1 (.fixedRedInternal atom slot element)
        (fixedRedInternalRed_mem
          source atom atomMember slot slotMember kindEq element)
        cell
    rw [TypedProblem.redIncidentValues,
      problem_redIncidences_fixedRedInternal
        source atom atomMember slot slotMember kindEq element] at cover
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using cover
  have greenCover (element : FixedRedInternalGreen) :
      PeriodicOneInThree.ExactlyOne
        (((fixedRedPhysicalGreen element).neighbors).map fun triple =>
          matching (.fixedRed atom slot triple) cell) := by
    have cover :=
      satisfies.2.1 (.fixedRedInternal atom slot element)
        (fixedRedInternalGreen_mem
          source atom atomMember slot slotMember kindEq element)
        cell
    rw [TypedProblem.greenIncidentValues,
      problem_greenIncidences_fixedRedInternal
        source atom atomMember slot slotMember kindEq element] at cover
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using cover
  have blueCover (element : FixedRedInternalBlue) :
      PeriodicOneInThree.ExactlyOne
        (((fixedRedPhysicalBlue element).neighbors).map fun triple =>
          matching (.fixedRed atom slot triple) cell) := by
    have cover :=
      satisfies.2.2 (.fixedRedInternal atom slot element)
        (fixedRedInternalBlue_mem
          source atom atomMember slot slotMember kindEq element)
        cell
    rw [TypedProblem.blueIncidentValues,
      problem_blueIncidences_fixedRedInternal
        source atom atomMember slot slotMember kindEq element] at cover
    simpa [TypedProblem.incidenceValue, Cell.sub,
      List.map_map, Function.comp_def] using cover
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [fixedRedPhysicalRed] using redCover .middleRung
  · simpa [fixedRedPhysicalRed] using redCover .topAuxiliary
  · simpa [fixedRedPhysicalGreen] using greenCover .leftRung
  · simpa [fixedRedPhysicalGreen] using greenCover .topRightLink
  · simpa [fixedRedPhysicalGreen] using greenCover .bottomRightLink
  · simpa [fixedRedPhysicalBlue] using blueCover .topLeftLink
  · simpa [fixedRedPhysicalBlue] using blueCover .bottomLeftLink
  · simpa [fixedRedPhysicalBlue] using blueCover .rightRung

private theorem clauseInternalRed_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    RedElement.clauseInternal clauseIndex ∈ redElements source := by
  simp only [redElements, List.mem_append, List.mem_flatMap]
  right
  exact ⟨clauseIndex, List.mem_range.mpr indexLt, by simp⟩

private theorem clauseInternalGreen_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    GreenElement.clauseInternal clauseIndex ∈ greenElements source := by
  simp only [greenElements, List.mem_append, List.mem_flatMap]
  right
  exact ⟨clauseIndex, List.mem_range.mpr indexLt, by simp⟩

private theorem clauseInternalBlue_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length) :
    BlueElement.clauseInternal clauseIndex ∈ blueElements source := by
  simp only [blueElements, List.mem_append, List.mem_flatMap]
  right
  exact ⟨clauseIndex, List.mem_range.mpr indexLt, by simp⟩

/-- A global perfect matching covers each of the three internal elements of
one clause core exactly once. -/
theorem clauseInternal_holds_of_satisfies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (matching : (problem source).MatchingAssignment)
    (satisfies : (problem source).Satisfies matching)
    (clauseIndex : Nat) (indexLt : clauseIndex < source.clauses.length)
    (cell : Cell) :
    ∀ element : X3CClauseInternal,
      PeriodicOneInThree.ExactlyOne
        (element.neighbors.map fun set =>
          matching (.clause clauseIndex set) cell) := by
  intro element
  cases element with
  | left =>
      have cover :=
        satisfies.1 (.clauseInternal clauseIndex)
          (clauseInternalRed_mem source clauseIndex indexLt) cell
      rw [TypedProblem.redIncidentValues,
        problem_redIncidences_clauseInternal
          source clauseIndex indexLt] at cover
      simpa [X3CClauseInternal.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using cover
  | right =>
      have cover :=
        satisfies.2.1 (.clauseInternal clauseIndex)
          (clauseInternalGreen_mem source clauseIndex indexLt) cell
      rw [TypedProblem.greenIncidentValues,
        problem_greenIncidences_clauseInternal
          source clauseIndex indexLt] at cover
      simpa [X3CClauseInternal.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using cover
  | bottom =>
      have cover :=
        satisfies.2.2 (.clauseInternal clauseIndex)
          (clauseInternalBlue_mem source clauseIndex indexLt) cell
      rw [TypedProblem.blueIncidentValues,
        problem_blueIncidences_clauseInternal
          source clauseIndex indexLt] at cover
      simpa [X3CClauseInternal.neighbors,
        TypedProblem.incidenceValue, Cell.sub,
        List.map_map, Function.comp_def] using cover

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
