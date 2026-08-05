import LeanTrominoes.PeriodicEightOccurrenceSplitCycleMacrocellSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitOccurrences
import LeanTrominoes.PeriodicMacrocellGeometry

/-!
# Fundamental-square bounds for positioned fixed-eight splitting

The factor-36 occurrence-splitting construction places copied clauses at
scaled source-clause positions and places every ring variable and implication
clause within six cells of a scaled source-variable position.  Thus strict
fundamental-square bounds for the source variable and stored clause vertices
transport to strict bounds for all stored vertices of the split formula.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicThreeSATThree

/-- Every occurring split variable remains strictly inside the refined
fundamental square, provided every occurring source variable is inside the
source square. -/
theorem placement_position_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourceVariableInside :
      ∀ atom ∈ sourceVariables source.erase,
        0 < (sourcePlacement.position atom).1 ∧
          (sourcePlacement.position atom).1 < sourcePlacement.period ∧
        0 < (sourcePlacement.position atom).2 ∧
          (sourcePlacement.position atom).2 < sourcePlacement.period)
    (occurrence : ThreeOccurrenceVariable Variable)
    (occurrenceMember :
      occurrence ∈
        (formula source sourcePlacement occurrencePorts).erase.variableOccurrences) :
    0 < ((placement sourcePlacement).position occurrence).1 ∧
      ((placement sourcePlacement).position occurrence).1 <
        (placement sourcePlacement).period ∧
      0 < ((placement sourcePlacement).position occurrence).2 ∧
      ((placement sourcePlacement).position occurrence).2 <
        (placement sourcePlacement).period := by
  rw [erase_formula] at occurrenceMember
  have ownerMember : occurrence.1 ∈ sourceVariables source.erase :=
    PeriodicEightOccurrenceSplit.formula_variableOccurrences_fst_mem_sourceVariables
      source.erase occurrencePorts occurrenceMember
  have ownerInside := sourceVariableInside occurrence.1 ownerMember
  let offset :=
    Cell.sub
      (ringVariablePosition
        (PeriodicEightOccurrenceSplit.ringVertexOfIndex occurrence.2.1))
      (12, 12)
  have offsetInside : Cell.PositionInMacrocellHalo 36 offset := by
    have bounded :=
      ringVariablePosition_inClosedGridRectangle
        (PeriodicEightOccurrenceSplit.ringVertexOfIndex occurrence.2.1)
    simp only [InClosedGridRectangle] at bounded
    simp only [Cell.PositionInMacrocellHalo, offset, Cell.sub]
    omega
  have refinedInside :=
    Cell.macrocellPosition_halo_in_refined_square
      (factor := 36) (period := sourcePlacement.period)
      (by decide) ownerInside offsetInside
  have positionEq :
      (placement sourcePlacement).position occurrence =
        Cell.macrocellPosition 36
          (sourcePlacement.position occurrence.1) offset := by
    apply Prod.ext <;>
      simp [placement, refinementScale, occurrenceVariablePosition,
        macroOrigin, offset, Cell.macrocellPosition,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  rw [positionEq]
  simpa [placement, refinementScale] using refinedInside

/-- Every stored split-clause position remains strictly inside the refined
fundamental square, provided source variables and stored source clauses are
inside the source square. -/
theorem storedClausePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts :
      PeriodicEightOccurrenceSplit.OccurrencePorts)
    (sourceVariableInside :
      ∀ atom ∈ sourceVariables source.erase,
        0 < (sourcePlacement.position atom).1 ∧
          (sourcePlacement.position atom).1 < sourcePlacement.period ∧
        0 < (sourcePlacement.position atom).2 ∧
          (sourcePlacement.position atom).2 < sourcePlacement.period)
    (sourceClauseInside :
      ∀ clause ∈ source.clauses,
        0 < clause.position.1 ∧
          clause.position.1 < sourcePlacement.period ∧
        0 < clause.position.2 ∧
          clause.position.2 < sourcePlacement.period)
    (clause : PositionedPeriodicClause
      (ThreeOccurrenceVariable Variable))
    (clauseMember :
      clause ∈ (formula source sourcePlacement occurrencePorts).clauses) :
    0 < clause.position.1 ∧
      clause.position.1 < (placement sourcePlacement).period ∧
      0 < clause.position.2 ∧
      clause.position.2 < (placement sourcePlacement).period := by
  rw [formula] at clauseMember
  rcases List.mem_append.mp clauseMember with
      occurrenceClauseMember | cycleClauseMember
  · rw [occurrenceClauses] at occurrenceClauseMember
    rcases List.mem_map.mp occurrenceClauseMember with
      ⟨taggedClause, taggedClauseMember, rfl⟩
    have sourceInside :=
      sourceClauseInside taggedClause.1
        (List.fst_mem_of_mem_zipIdx taggedClauseMember)
    cases sourcePositionEq : taggedClause.1.position with
    | mk sourceX sourceY =>
    simp only [occurrenceClause, placement, refinementScale,
      Cell.scale, sourcePositionEq] at sourceInside ⊢
    norm_num at sourceInside ⊢
    exact
      ⟨by nlinarith, by nlinarith,
        by nlinarith, by nlinarith⟩
  · rw [allCycleClauses, List.mem_flatMap] at cycleClauseMember
    rcases cycleClauseMember with
      ⟨atom, atomMember, localClauseMember⟩
    rcases List.mem_iff_getElem.mp localClauseMember with
      ⟨clauseIndex, clauseIndexLt, clauseAt⟩
    have taggedClauseMember :
        (clause, clauseIndex) ∈
          (cycleClausesFor sourcePlacement atom).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
      exact ⟨clauseIndexLt, clauseAt⟩
    have localBounded :=
      positionedCycleClausePosition_inClosedGridRectangle
        sourcePlacement atom taggedClauseMember
    have ownerInside := sourceVariableInside atom atomMember
    cases ownerPositionEq : sourcePlacement.position atom with
    | mk ownerX ownerY =>
    cases clausePositionEq : clause.position with
    | mk clauseX clauseY =>
    simp only [positionedCycleRouteLower, positionedCycleRouteUpper,
      macroOrigin, InClosedGridRectangle, Cell.add, Cell.sub, Cell.scale,
      refinementScale, ownerPositionEq, clausePositionEq] at localBounded
    simp only [placement, refinementScale, ownerPositionEq] at ownerInside ⊢
    norm_num at localBounded ownerInside ⊢
    exact
      ⟨by nlinarith, by nlinarith,
        by nlinarith, by nlinarith⟩

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
