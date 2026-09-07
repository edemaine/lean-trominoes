/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanProjections

/-! # Clause fan fields at their actual clause and literal indices -/

namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

variable {Variable : Type*} [DecidableEq Variable]
variable {source : PositionedPeriodicCNF Variable}
variable {placement : PeriodicVariablePlacement Variable}
variable (presentation : source.PlanarIncidencePresentation placement)

private theorem indexedClauseIndex_eq
    (clauseIndex : Nat) (entry : ActiveOccurrenceEntry source.erase)
    (member : entry ∈ activeClauseOccurrenceEntries source.erase clauseIndex) :
    (occurrenceSpliceData presentation entry).indexed.1.clauseIndex = clauseIndex :=
  (occurrenceClauseIndex_eq_indexedClauseIndex presentation entry).symm.trans
    ((mem_activeClauseOccurrenceEntries_iff source.erase clauseIndex entry).mp member)

include presentation in
/-- An occurrence belonging to a genuine clause has a literal index inside
that same clause, independently of the variable-major enumeration order. -/
theorem occurrenceLiteralIndex_lt_of_clauseMember
    {clause : PositionedPeriodicClause Variable} {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx)
    (entry : ActiveOccurrenceEntry source.erase)
    (member : entry ∈ activeClauseOccurrenceEntries source.erase clauseIndex) :
    occurrenceLiteralIndex source.erase entry.1.1 entry.1.2 < clause.literals.length := by
  let data := occurrenceSpliceData presentation entry
  have parts := (PeriodicCNF.mem_incidencesWithMetadata_iff source.erase data.indexed.1).mp
    (List.fst_mem_of_mem_zipIdx data.indexedMember)
  have erasedLookup : source.erase.clauses[clauseIndex]? = some clause.literals := by
    simp only [PositionedPeriodicCNF.erase, List.getElem?_map,
      (List.mem_zipIdx_iff_getElem?).mp clauseMember, Option.map_some]
  have indexEq := indexedClauseIndex_eq presentation clauseIndex entry member
  have lookup := (List.mem_zipIdx_iff_getElem?).mp parts.1
  rw [indexEq, erasedLookup] at lookup
  have clauseEq : clause.literals = data.indexed.1.clause := Option.some.inj lookup
  have literalLt : data.indexed.1.literalIndex < clause.literals.length := by
    rw [clauseEq]
    exact List.snd_lt_of_mem_zipIdx parts.2
  simpa only [occurrenceLiteralIndex_eq_indexedLiteralIndex presentation entry] using literalLt

private theorem literalIndexOfTerminalGroup_of_lt_three (index : Nat) (lt : index < 3) :
    literalIndexOfTerminalGroup (terminalGroupOfLiteralIndex index) = index := by
  interval_cases index <;> rfl

include presentation in
private theorem literalIndex_eq_of_group
    (width : source.erase.WidthAtMost 3)
    {clause : PositionedPeriodicClause Variable} {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx)
    (entry : ActiveOccurrenceEntry source.erase)
    (member : entry ∈ activeClauseOccurrenceEntries source.erase clauseIndex)
    (group : X3CClauseTerminalGroup)
    (groupEq : occurrenceClauseTerminalGroup source.erase entry = group) :
    occurrenceLiteralIndex source.erase entry.1.1 entry.1.2 = literalIndexOfTerminalGroup group := by
  have bound := occurrenceLiteralIndex_lt_of_clauseMember presentation clauseMember entry member
  have clauseWidth : clause.literals.length ≤ 3 := width clause.literals
    (List.mem_map.mpr ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩)
  have inverse := literalIndexOfTerminalGroup_of_lt_three
    (occurrenceLiteralIndex source.erase entry.1.1 entry.1.2) (by omega)
  change terminalGroupOfLiteralIndex
    (occurrenceLiteralIndex source.erase entry.1.1 entry.1.2) = group at groupEq
  rw [groupEq] at inverse
  exact inverse.symm

/-- The semantic fan selects the incoming stored-route direction at the
terminal's actual literal index, and uses north precisely when it is absent. -/
theorem sourceClauseRibbonFanData_direction_eq_indexedRoute
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    {clause : PositionedPeriodicClause Variable} {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx)
    (group : X3CClauseTerminalGroup) :
    (sourceClauseRibbonFanData presentation clauseIndex).direction group =
      if literalIndexOfTerminalGroup group < clause.literals.length then
        (AxisDirection.polylineFirstDirection
          (presentation.routes clauseIndex (literalIndexOfTerminalGroup group))).opposite
      else .north := by
  by_cases active : literalIndexOfTerminalGroup group < clause.literals.length
  · rw [if_pos active]
    obtain ⟨entry, member, literalEq⟩ :=
      exists_activeClauseOccurrenceEntry_of_literalIndex occurrences clauseMember active
    have groupEq : occurrenceClauseTerminalGroup source.erase entry = group := by
      simp only [occurrenceClauseTerminalGroup, literalEq,
        terminalGroupOfLiteralIndex_literalIndexOfTerminalGroup]
    have direction := ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
      presentation width clauseIndex entry member
    rw [groupEq] at direction
    have indexEq := indexedClauseIndex_eq presentation clauseIndex entry member
    have literalIndexEq :=
      (occurrenceLiteralIndex_eq_indexedLiteralIndex presentation entry).symm.trans literalEq
    simpa only [indexEq, literalIndexEq] using direction.trans
      (occurrenceSourceClauseDirection_eq_storedRoute presentation entry)
  · have absent :
        (activeClauseOccurrenceEntries source.erase clauseIndex).find?
            (fun entry => decide (occurrenceClauseTerminalGroup source.erase entry = group)) = none := by
      apply List.find?_eq_none.mpr
      intro entry member predicateTrue
      have literalEq := literalIndex_eq_of_group presentation width clauseMember
        entry member group (of_decide_eq_true predicateTrue)
      have literalLt := occurrenceLiteralIndex_lt_of_clauseMember presentation clauseMember entry member
      rw [literalEq] at literalLt
      exact active literalLt
    rw [sourceClauseRibbonFanData_direction_eq, absent, if_neg active]

/-- A genuine width-three clause has a right terminal exactly when its
third literal exists. -/
theorem sourceClauseRibbonFanData_hasRight_eq_arity
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    {clause : PositionedPeriodicClause Variable} {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈ source.clauses.zipIdx) :
    (sourceClauseRibbonFanData presentation clauseIndex).hasRight =
      decide (3 ≤ clause.literals.length) := by
  by_cases active : 3 ≤ clause.literals.length
  · obtain ⟨entry, member, literalEq⟩ :=
      exists_activeClauseOccurrenceEntry_of_literalIndex occurrences clauseMember
        (literalIndex := 2) (by omega)
    have right : occurrenceClauseTerminalGroup source.erase entry = .right := by
      simp only [occurrenceClauseTerminalGroup, literalEq, terminalGroupOfLiteralIndex]
    have hasRight := (ClauseRibbonFanData.sourceClauseRibbonFanData_hasRight_iff
      presentation clauseIndex).mpr ⟨entry, member, right⟩
    simpa only [active, decide_true] using hasRight
  · have noRight : ¬ (sourceClauseRibbonFanData presentation clauseIndex).hasRight = true := by
      intro hasRight
      obtain ⟨entry, member, right⟩ :=
        (ClauseRibbonFanData.sourceClauseRibbonFanData_hasRight_iff presentation clauseIndex).mp hasRight
      have literalEq := literalIndex_eq_of_group presentation width clauseMember entry member .right right
      have literalLt := occurrenceLiteralIndex_lt_of_clauseMember presentation clauseMember entry member
      rw [literalEq] at literalLt
      change 2 < clause.literals.length at literalLt
      omega
    simpa only [active, decide_false] using Bool.eq_false_of_not_eq_true noRight

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
