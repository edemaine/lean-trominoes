/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsClauseRouteOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFanOrder

/-!
# Unit-elimination route order supplies source clause fans

The generic coordinated clause fan needs the three incoming directions in
literal order.  This file packages the route-level invariant supplied by
unit elimination: every ternary stored route initially leaves its clause
toward south, west, or east according to literal index `0`, `1`, or `2`.

That invariant is proved for every spliced unit-elimination route family.
Reversing the stored clause-to-variable directions gives the incoming
north/east/west order, which is exactly the clockwise order required by the
finite clause-fan table.  Binary clauses are shown to have no active right
terminal and are therefore compatible automatically.
-/

namespace LeanTrominoes

namespace PositionedPeriodicCNF

/-- Every ternary incidence route leaves its stored clause in the canonical
unit-elimination literal-index order. -/
def TernaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ indexed :
      CNFIncidence Variable × Nat,
    indexed ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx →
    indexed.1.clause.length = 3 →
    AxisDirection.polylineFirstDirection
        (routes indexed.1.clauseIndex indexed.1.literalIndex) =
      AxisDirection.unitEliminationClauseExitDirection
        indexed.1.literalIndex

/-- Every unit-elimination route family obtained by splicing arbitrary
inherited suffixes has the canonical ternary clause order. -/
theorem splicedRoutes_ternaryClauseRoutesInUnitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (inherited :
      InheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula source)
        (PeriodicOneInThreeNoUnitsPositioned.placement
          source sourcePlacement)
        (PeriodicOneInThreeNoUnitsPositioned.normalizedLocalEndpoint
          source sourcePlacement)) :
    TernaryClauseRoutesInUnitEliminationOrder
      (PeriodicOneInThreeNoUnitsPositioned.formula source)
      (PeriodicOneInThreeNoUnitsPositioned.splicedRoutes
        source sourcePlacement inherited) := by
  intro indexed indexedMember arity
  have incidenceMember :
      indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata
          (PeriodicOneInThreeNoUnitsPositioned.formula source).erase :=
    List.fst_mem_of_mem_zipIdx indexedMember
  have members :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff
      (PeriodicOneInThreeNoUnitsPositioned.formula source).erase
      indexed.1).mp incidenceMember
  rcases members with ⟨clauseMember, indexedLiteralMember⟩
  change
    (indexed.1.clause, indexed.1.clauseIndex) ∈
      ((PeriodicOneInThreeNoUnitsPositioned.formula
        source).clauses.map PositionedPeriodicClause.literals).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, clauseEq⟩
  have indexEq : taggedClause.2 = indexed.1.clauseIndex :=
    congrArg Prod.snd clauseEq
  have literalsEq :
      taggedClause.1.literals = indexed.1.clause :=
    congrArg Prod.fst clauseEq
  have literalMember :
      (indexed.1.literal, indexed.1.literalIndex) ∈
        taggedClause.1.literals.zipIdx := by
    simpa [literalsEq] using indexedLiteralMember
  have result :=
    PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_firstDirection_of_ternary
      source sourcePlacement sourceWidth inherited
      taggedClauseMember
      (by simpa [literalsEq] using arity)
      literalMember
  simpa [indexEq] using result

end PositionedPeriodicCNF

namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- An indexed erased incidence and its positioned clause at the same index
carry the same literal list. -/
theorem indexedIncidence_clause_eq_positionedClause_literals
    {Variable : Type*}
    {source : PositionedPeriodicCNF Variable}
    {indexed : CNFIncidence Variable × Nat}
    (indexedMember :
      indexed ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx)
    {positionedClause : PositionedPeriodicClause Variable}
    (clauseMember :
      (positionedClause, indexed.1.clauseIndex) ∈
        source.clauses.zipIdx) :
    indexed.1.clause = positionedClause.literals := by
  have incidenceMember :
      indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx indexedMember
  have indexedClauseMember :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff
      source.erase indexed.1).mp incidenceMember |>.1
  have positionedClauseMember :
      (positionedClause.literals, indexed.1.clauseIndex) ∈
        source.erase.clauses.zipIdx := by
    change
      (positionedClause.literals, indexed.1.clauseIndex) ∈
        (source.clauses.map
          PositionedPeriodicClause.literals).zipIdx
    rw [List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(positionedClause, indexed.1.clauseIndex),
        clauseMember, rfl⟩
  exact
    (List.mem_zipIdx' indexedClauseMember).2.trans
      (List.mem_zipIdx' positionedClauseMember).2.symm

/-- A ternary occurrence in a canonically ordered route family enters its
clause opposite the corresponding unit-elimination exit direction. -/
theorem occurrenceSourceClauseDirection_of_unitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder
        presentation.routes)
    (entry : ActiveOccurrenceEntry source.erase)
    (arity :
      (occurrenceSpliceData presentation entry)
        |>.indexed.1.clause.length = 3) :
    occurrenceSourceClauseDirection presentation entry =
      (AxisDirection.unitEliminationClauseExitDirection
        (occurrenceLiteralIndex source.erase
          entry.1.1 entry.1.2)).opposite := by
  let data := occurrenceSpliceData presentation entry
  rw [occurrenceSourceClauseDirection_eq_storedRoute]
  rw [ordered data.indexed data.indexedMember arity]
  rw [occurrenceLiteralIndex_eq_indexedLiteralIndex
    presentation entry]

/-- The three directions of a ternary source clause fan are clockwise when
the stored route family has unit-elimination order. -/
theorem sourceClauseRibbonFanData_clockwise_of_unitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder
        presentation.toPlanarIncidencePresentation.routes)
    (entry : ActiveOccurrenceEntry source.erase)
    {positionedClause : PositionedPeriodicClause Variable}
    (clauseMember :
      (positionedClause,
        occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2) ∈ source.clauses.zipIdx)
    (arity : positionedClause.literals.length = 3) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    AxisDirection.InClockwiseOrder
      (data.direction .top)
      (data.direction .left)
      (data.direction .right) := by
  let planar := presentation.toPlanarIncidencePresentation
  let clauseIndex :=
    occurrenceClauseIndex source.erase entry.1.1 entry.1.2
  let data := sourceClauseRibbonFanData planar clauseIndex
  dsimp only
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 0) (by omega) with
    ⟨topEntry, topMember, topIndex⟩
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 1) (by omega) with
    ⟨leftEntry, leftMember, leftIndex⟩
  rcases exists_activeClauseOccurrenceEntry_of_literalIndex
      occurrences clauseMember (literalIndex := 2) (by omega) with
    ⟨rightEntry, rightMember, rightIndex⟩
  have candidateDirection :
      ∀ (candidate : ActiveOccurrenceEntry source.erase)
        (candidateMember :
          candidate ∈
            activeClauseOccurrenceEntries source.erase clauseIndex)
        (literalIndex : Nat)
        (indexEq :
          occurrenceLiteralIndex source.erase
            candidate.1.1 candidate.1.2 = literalIndex),
        occurrenceSourceClauseDirection planar candidate =
          (AxisDirection.unitEliminationClauseExitDirection
            literalIndex).opposite := by
    intro candidate candidateMember literalIndex indexEq
    let candidateData := occurrenceSpliceData planar candidate
    have candidateIndexEq :
        candidateData.indexed.1.clauseIndex = clauseIndex := by
      calc
        candidateData.indexed.1.clauseIndex =
            occurrenceClauseIndex source.erase
              candidate.1.1 candidate.1.2 :=
          (occurrenceClauseIndex_eq_indexedClauseIndex
            planar candidate).symm
        _ = clauseIndex :=
          (mem_activeClauseOccurrenceEntries_iff
            source.erase clauseIndex candidate).mp candidateMember
    have candidateClauseMember :
        (positionedClause,
          candidateData.indexed.1.clauseIndex) ∈
            source.clauses.zipIdx := by
      simpa [candidateIndexEq] using clauseMember
    have candidateClauseEq :
        candidateData.indexed.1.clause =
          positionedClause.literals :=
      indexedIncidence_clause_eq_positionedClause_literals
        candidateData.indexedMember candidateClauseMember
    have candidateArity :
        candidateData.indexed.1.clause.length = 3 := by
      rw [candidateClauseEq, arity]
    rw [occurrenceSourceClauseDirection_of_unitEliminationOrder
      planar ordered candidate candidateArity, indexEq]
  have topDirection :
      data.direction .top = .north := by
    calc
      data.direction .top =
          data.direction
            (occurrenceClauseTerminalGroup source.erase topEntry) := by
        simp [occurrenceClauseTerminalGroup, topIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar topEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex topEntry topMember
      _ = .north := by
        rw [candidateDirection topEntry topMember 0 topIndex]
        rfl
  have leftDirection :
      data.direction .left = .east := by
    calc
      data.direction .left =
          data.direction
            (occurrenceClauseTerminalGroup source.erase leftEntry) := by
        simp [occurrenceClauseTerminalGroup, leftIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar leftEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex leftEntry leftMember
      _ = .east := by
        rw [candidateDirection leftEntry leftMember 1 leftIndex]
        rfl
  have rightDirection :
      data.direction .right = .west := by
    calc
      data.direction .right =
          data.direction
            (occurrenceClauseTerminalGroup source.erase rightEntry) := by
        simp [occurrenceClauseTerminalGroup, rightIndex,
          terminalGroupOfLiteralIndex]
      _ = occurrenceSourceClauseDirection planar rightEntry :=
        ClauseRibbonFanData.sourceClauseRibbonFanData_direction_of_widthAtMostThree
            planar width clauseIndex rightEntry rightMember
      _ = .west := by
        rw [candidateDirection rightEntry rightMember 2 rightIndex]
        rfl
  rw [topDirection, leftDirection, rightDirection]
  native_decide

/-- A positioned binary clause has no active right terminal in its source
clause fan. -/
theorem sourceClauseRibbonFanData_noRight_of_binary
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    {positionedClause : PositionedPeriodicClause Variable}
    (clauseMember :
      (positionedClause,
        occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2) ∈ source.clauses.zipIdx)
    (arity : positionedClause.literals.length = 2) :
    (sourceClauseRibbonFanData presentation
      (occurrenceClauseIndex source.erase
        entry.1.1 entry.1.2)).hasRight = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hasRight
  rw [ClauseRibbonFanData.sourceClauseRibbonFanData_hasRight_iff]
    at hasRight
  rcases hasRight with
    ⟨candidate, candidateMember, candidateRight⟩
  let candidateData := occurrenceSpliceData presentation candidate
  have candidateIndexEq :
      candidateData.indexed.1.clauseIndex =
        occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2 := by
    calc
      candidateData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            candidate.1.1 candidate.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          presentation candidate).symm
      _ = occurrenceClauseIndex source.erase
            entry.1.1 entry.1.2 :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase
          (occurrenceClauseIndex source.erase
            entry.1.1 entry.1.2)
          candidate).mp candidateMember
  have candidateClauseMember :
      (positionedClause,
        candidateData.indexed.1.clauseIndex) ∈
          source.clauses.zipIdx := by
    simpa [candidateIndexEq] using clauseMember
  have candidateClauseEq :
      candidateData.indexed.1.clause =
        positionedClause.literals :=
    indexedIncidence_clause_eq_positionedClause_literals
      candidateData.indexedMember candidateClauseMember
  have incidenceMember :
      candidateData.indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx candidateData.indexedMember
  have literalLt :
      candidateData.indexed.1.literalIndex <
        candidateData.indexed.1.clause.length :=
    List.snd_lt_of_mem_zipIdx
      ((PeriodicCNF.mem_incidencesWithMetadata_iff
        source.erase candidateData.indexed.1).mp incidenceMember).2
  have occurrenceLt :
      occurrenceLiteralIndex source.erase
        candidate.1.1 candidate.1.2 < 2 := by
    rw [occurrenceLiteralIndex_eq_indexedLiteralIndex
      presentation candidate]
    simpa [candidateClauseEq, arity] using literalLt
  have indexCases :
      occurrenceLiteralIndex source.erase
          candidate.1.1 candidate.1.2 = 0 ∨
        occurrenceLiteralIndex source.erase
          candidate.1.1 candidate.1.2 = 1 := by
    omega
  rcases indexCases with indexEq | indexEq <;>
    simp [occurrenceClauseTerminalGroup, indexEq,
      terminalGroupOfLiteralIndex] at candidateRight

/-- Unit-elimination route order discharges the complete source clause-fan
compatibility obligation. -/
theorem sourceClauseRibbonFanData_isClockwiseCompatible_of_unitEliminationOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (ordered :
      source.TernaryClauseRoutesInUnitEliminationOrder
        presentation.toPlanarIncidencePresentation.routes)
    (entry : ActiveOccurrenceEntry source.erase) :
    let planar := presentation.toPlanarIncidencePresentation
    let data := sourceClauseRibbonFanData planar
      (occurrenceClauseIndex source.erase entry.1.1 entry.1.2)
    data.IsClockwiseCompatible := by
  let planar := presentation.toPlanarIncidencePresentation
  rcases exists_positionedClause_of_activeOccurrenceEntry
      planar entry with
    ⟨positionedClause, clauseMember⟩
  have erasedClauseMember :
      positionedClause.literals ∈ source.erase.clauses := by
    change positionedClause.literals ∈
      source.clauses.map PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨positionedClause,
        List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
  rcases arity positionedClause.literals erasedClauseMember with
    binary | ternary
  · apply sourceClauseRibbonFanData_isClockwiseCompatible_of_noRight
      presentation width occurrences arity entry
    exact sourceClauseRibbonFanData_noRight_of_binary
      planar entry clauseMember binary
  · apply sourceClauseRibbonFanData_isClockwiseCompatible_of_clockwise
      presentation width occurrences arity entry
    exact sourceClauseRibbonFanData_clockwise_of_unitEliminationOrder
      presentation width occurrences ordered entry
      clauseMember ternary

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
