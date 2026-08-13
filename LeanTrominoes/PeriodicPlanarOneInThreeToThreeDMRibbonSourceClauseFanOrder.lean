/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanUniqueness
import LeanTrominoes.PeriodicOneInThreeNoUnits

/-!
# Clockwise order of source clause ribbon fans

The finite clause-fan table needs every active top, left, or right terminal
to carry a genuine direction, distinct from every other active terminal.
This file derives those facts from source planarity.  The source occurrence
bound reifies every literal index as an active occurrence entry, while the
two-or-three arity condition proves that every active finite terminal has
such an entry.

Consequently a source clause fan is table-compatible exactly when its
optional third direction occurs after the top and left directions in
clockwise cyclic order.  Binary clauses require no further condition.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Every literal of a source clause is represented by an active occurrence
entry in that clause orbit. -/
theorem exists_activeClauseOccurrenceEntry_of_literalIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (occurrences : source.erase.OccurrencesAtMost 3)
    {positionedClause : PositionedPeriodicClause Variable}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (positionedClause, clauseIndex) ∈ source.clauses.zipIdx)
    (literalLt : literalIndex < positionedClause.literals.length) :
    ∃ entry : ActiveOccurrenceEntry source.erase,
      entry ∈
        activeClauseOccurrenceEntries source.erase clauseIndex ∧
      occurrenceLiteralIndex source.erase entry.1.1 entry.1.2 =
        literalIndex := by
  let literal := positionedClause.literals[literalIndex]
  let tagged : TaggedOccurrence Variable :=
    (literal, clauseIndex, literalIndex)
  have erasedClauseMember :
      (positionedClause.literals, clauseIndex) ∈
        source.erase.clauses.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    have clauseLookup :=
      (List.mem_zipIdx_iff_getElem?).mp clauseMember
    simp [PositionedPeriodicCNF.erase, clauseLookup]
  have literalMember :
      (literal, literalIndex) ∈
        positionedClause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_getElem literalLt
  have taggedMember :
      tagged ∈
        PeriodicThreeSATThree.taggedLiterals source.erase := by
    exact PeriodicThreeSATThree.taggedLiterals_mem
      source.erase erasedClauseMember literalMember
  rcases
      PeriodicOneInThreeToThreeDM.exists_occurrenceSlot
        source.erase occurrences tagged taggedMember with
    ⟨slot, lookup⟩
  have atomMember :
      tagged.1.atom ∈ occurringVariables source.erase :=
    PeriodicOneInThreeToThreeDM.atom_mem_occurringVariables_of_tagged_mem
      source.erase tagged taggedMember
  have slotMember :
      slot ∈ usedSlots source.erase tagged.1.atom := by
    simp only [usedSlots, List.mem_filter]
    constructor
    · cases slot <;>
        simp [allOccurrenceSlots,
          PeriodicOneInThreeToThreeDM.OccurrenceSlot.all]
    · exact Option.isSome_iff_exists.mpr ⟨tagged, lookup⟩
  let entry : ActiveOccurrenceEntry source.erase :=
    ⟨(tagged.1.atom, slot),
      (mem_occurrenceEntries_iff
        source.erase tagged.1.atom slot).mpr
        ⟨atomMember, slotMember⟩⟩
  refine ⟨entry, ?_, ?_⟩
  · rw [mem_activeClauseOccurrenceEntries_iff]
    exact occurrenceClauseIndex_of_occurrenceAt
      source.erase tagged.1.atom slot tagged lookup
  · exact occurrenceLiteralIndex_of_occurrenceAt
      source.erase tagged.1.atom slot tagged lookup

/-- Recover the positioned source clause represented by an active occurrence
entry. -/
theorem exists_positionedClause_of_activeOccurrenceEntry
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    ∃ positionedClause,
      (positionedClause,
          occurrenceClauseIndex source.erase
            entry.1.1 entry.1.2) ∈ source.clauses.zipIdx := by
  let data := occurrenceSpliceData presentation entry
  refine ⟨data.positionedClause, ?_⟩
  have indexEq :=
    occurrenceClauseIndex_eq_indexedClauseIndex
      presentation entry
  simpa [data, indexEq] using data.clauseMember

/-- Every active finite clause-fan group is represented by a source
occurrence. -/
theorem sourceClauseRibbonFanData_exists_entry_of_groupActive
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase)
    (group : PlanarThreeDM.X3CClauseTerminalGroup)
    (active :
      (sourceClauseRibbonFanData presentation
        (occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2)).GroupActive group) :
    ∃ candidate : ActiveOccurrenceEntry source.erase,
      candidate ∈
        activeClauseOccurrenceEntries source.erase
          (occurrenceClauseIndex source.erase
            entry.1.1 entry.1.2) ∧
      occurrenceClauseTerminalGroup source.erase candidate =
        group := by
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData presentation clauseIndex
  rcases
      exists_positionedClause_of_activeOccurrenceEntry presentation entry with
    ⟨positionedClause, clauseMember⟩
  have erasedClauseMember :
      positionedClause.literals ∈ source.erase.clauses := by
    change positionedClause.literals ∈
      source.clauses.map PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨positionedClause,
        List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
  have clauseArity :
      positionedClause.literals.length = 2 ∨
        positionedClause.literals.length = 3 :=
    arity positionedClause.literals erasedClauseMember
  cases group with
  | top =>
      rcases exists_activeClauseOccurrenceEntry_of_literalIndex
          occurrences clauseMember
          (literalIndex := 0) (by omega) with
        ⟨candidate, candidateMember, literalIndex⟩
      refine ⟨candidate, candidateMember, ?_⟩
      simp [occurrenceClauseTerminalGroup, literalIndex,
        terminalGroupOfLiteralIndex]
  | left =>
      rcases exists_activeClauseOccurrenceEntry_of_literalIndex
          occurrences clauseMember
          (literalIndex := 1) (by omega) with
        ⟨candidate, candidateMember, literalIndex⟩
      refine ⟨candidate, candidateMember, ?_⟩
      simp [occurrenceClauseTerminalGroup, literalIndex,
        terminalGroupOfLiteralIndex]
  | right =>
      have hasRight : data.hasRight = true := by
        by_contra notRight
        have noRight : data.hasRight = false :=
          Bool.eq_false_of_not_eq_true notRight
        change
          PlanarThreeDM.X3CClauseTerminalGroup.right ∈
            data.activeGroups at active
        simp [ClauseRibbonFanData.activeGroups, noRight] at active
      rw [ClauseRibbonFanData.sourceClauseRibbonFanData_hasRight_iff]
        at hasRight
      exact hasRight

/-- Every active direction in a source clause fan is genuine. -/
theorem sourceClauseRibbonFanData_genuine
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    ∀ group, data.GroupActive group →
      (data.direction group).IsGenuine := by
  let planar := presentation.toPlanarIncidencePresentation
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  dsimp only
  intro group active
  rcases
      sourceClauseRibbonFanData_exists_entry_of_groupActive
        planar occurrences arity entry group active with
    ⟨candidate, candidateMember, groupEq⟩
  rw [← groupEq]
  rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
      planar width clauseIndex candidate candidateMember]
  exact occurrenceSourceClauseDirection_isGenuine planar candidate

/-- Distinct active terminal groups in a source clause fan have distinct
directions. -/
theorem sourceClauseRibbonFanData_distinct
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    ∀ first second,
      data.GroupActive first →
      data.GroupActive second →
      first ≠ second →
      data.direction first ≠ data.direction second := by
  let planar := presentation.toPlanarIncidencePresentation
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  dsimp only
  intro first second firstActive secondActive groupsDifferent
  rcases
      sourceClauseRibbonFanData_exists_entry_of_groupActive
        planar occurrences arity entry first firstActive with
    ⟨firstEntry, firstMember, firstGroup⟩
  rcases
      sourceClauseRibbonFanData_exists_entry_of_groupActive
        planar occurrences arity entry second secondActive with
    ⟨secondEntry, secondMember, secondGroup⟩
  have entriesDifferent : firstEntry ≠ secondEntry := by
    intro equal
    subst secondEntry
    exact groupsDifferent (firstGroup.symm.trans secondGroup)
  have sameClause :
      let firstData := occurrenceSpliceData planar firstEntry
      let secondData := occurrenceSpliceData planar secondEntry
      firstData.indexed.1.clauseIndex =
        secondData.indexed.1.clauseIndex := by
    let firstData := occurrenceSpliceData planar firstEntry
    let secondData := occurrenceSpliceData planar secondEntry
    change
      firstData.indexed.1.clauseIndex =
        secondData.indexed.1.clauseIndex
    calc
      firstData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            firstEntry.1.1 firstEntry.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          planar firstEntry).symm
      _ = clauseIndex :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex firstEntry).mp firstMember
      _ = occurrenceClauseIndex source.erase
            secondEntry.1.1 secondEntry.1.2 :=
        ((mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex secondEntry).mp secondMember).symm
      _ = secondData.indexed.1.clauseIndex :=
        occurrenceClauseIndex_eq_indexedClauseIndex
          planar secondEntry
  have directionsDifferent :=
    occurrenceSourceClauseDirections_ne_of_same_clause
      presentation entriesDifferent sameClause
  rw [← firstGroup, ← secondGroup]
  rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
        planar width clauseIndex firstEntry firstMember,
    ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
        planar width clauseIndex secondEntry secondMember]
  exact directionsDifferent

/-- A source clause fan is table-compatible exactly when its optional
degree-three case occurs in clockwise literal order. -/
theorem sourceClauseRibbonFanData_isClockwiseCompatible_iff
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    data.IsClockwiseCompatible ↔
      (data.hasRight = true →
        AxisDirection.InClockwiseOrder
          (data.direction .top)
          (data.direction .left)
          (data.direction .right)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let data := sourceClauseRibbonFanData planar
    (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
  have genuine :=
    sourceClauseRibbonFanData_genuine
      presentation width occurrences arity entry
  have distinct :=
    sourceClauseRibbonFanData_distinct
      presentation width occurrences arity entry
  exact (ClauseRibbonFanData.isClockwiseCompatible_iff data).trans
    (and_iff_right genuine |>.trans (and_iff_right distinct))

/-- A binary source clause fan is automatically table-compatible. -/
theorem sourceClauseRibbonFanData_isClockwiseCompatible_of_noRight
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase)
    (noRight :
      let planar := presentation.toPlanarIncidencePresentation
      let data := sourceClauseRibbonFanData planar
        (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
      data.hasRight = false) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    data.IsClockwiseCompatible := by
  dsimp only at noRight ⊢
  apply
    (sourceClauseRibbonFanData_isClockwiseCompatible_iff
      presentation width occurrences arity entry).mpr
  intro hasRight
  rw [noRight] at hasRight
  contradiction

/-- A clockwise top-left-right source clause fan is table-compatible. -/
theorem sourceClauseRibbonFanData_isClockwiseCompatible_of_clockwise
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (entry : ActiveOccurrenceEntry source.erase)
    (clockwise :
      let planar := presentation.toPlanarIncidencePresentation
      let data := sourceClauseRibbonFanData planar
        (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
      AxisDirection.InClockwiseOrder
        (data.direction .top)
        (data.direction .left)
        (data.direction .right)) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    data.IsClockwiseCompatible := by
  dsimp only at clockwise ⊢
  apply
    (sourceClauseRibbonFanData_isClockwiseCompatible_iff
      presentation width occurrences arity entry).mpr
  exact fun _ => clockwise

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
