import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans
import LeanTrominoes.PeriodicOrthocrossingPlanarSATMacrocellCenters

/-!
# Uniqueness of source clause-fan terminal groups

The source clause-fan adapter looks up one incoming direction for each of
the top, left, and right terminal groups.  This file proves that lookup is
unambiguous for every width-three positioned periodic CNF presentation.

Each source endpoint is first normalized as a canonical clause vertex in
the open fundamental square plus an integral period translate.  Equality of
two lifted targets identifies their canonical clause vertices.  Width at
most three then makes the terminal group identify the literal index, and
the existing occurrence-slot uniqueness theorem identifies the active
source entries.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

private theorem occurrenceClauseVertex_member
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    CNFVertex.clause data.indexed.1.clauseIndex ∈
      source.erase.incidenceGraph.vertices := by
  let data := occurrenceSpliceData presentation entry
  have edgeMember :=
    PeriodicCNF.tagged_incidence_edge_mem
      source.erase data.indexedMember
  exact
    (presentation.compatible.1.2 data.indexed.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)).1

/-- A source occurrence's clause target is the canonical clause vertex
translated by the semantic rebasing offset of its stored incidence. -/
theorem occurrenceSourceClauseTarget_eq_liftedClauseVertex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    let drawing :=
      PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes
    occurrenceSourceClauseTarget presentation entry =
      Cell.add
        (PositionedPeriodicCNF.incidenceVertexPositionAt
          source placement (.clause data.indexed.1.clauseIndex))
        (drawing.periodTranslation
          (PositionedPeriodicCNF.variableToClauseTranslate
            data.indexed.1)) := by
  let data := occurrenceSpliceData presentation entry
  let drawing :=
    PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes
  have endpoints :=
    presentation.route_endpoints_of_tagged data.indexedMember
  have periodTranslationEq (offset : Cell) :
      drawing.periodTranslation offset =
        placement.translation offset := by
    unfold drawing PeriodicGridDrawing.periodTranslation
      PeriodicVariablePlacement.translation
    rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
      source placement presentation.routes
      presentation.periodPositive]
  have computed :
      (presentation.variableToClauseRoute
        data.indexed.1).getLast? =
      some
        (Cell.add
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement
              (.clause data.indexed.1.clauseIndex))
          (drawing.periodTranslation
            (PositionedPeriodicCNF.variableToClauseTranslate
              data.indexed.1))) := by
    simp only [
      PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute,
      translatePolyline, List.getLast?_map, List.getLast?_reverse,
      endpoints.1, Option.map_some]
    rw [periodTranslationEq]
    simp [PositionedPeriodicCNF.variableToClauseTranslate,
      Cell.add, add_comm]
  apply Option.some.inj
  exact data.routeLast.symm.trans computed

private theorem occurrenceClauseVertex_in_fundamentalSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    let drawing :=
      PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes
    drawing.PositionInFundamentalSquare
      (PositionedPeriodicCNF.incidenceVertexPositionAt
        source placement (.clause data.indexed.1.clauseIndex)) := by
  let data := occurrenceSpliceData presentation entry
  let drawing :=
    PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes
  have member :
      CNFVertex.clause data.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices :=
    occurrenceClauseVertex_member presentation entry
  have lookup :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes member
  change
    drawing.PositionInFundamentalSquare
      (PositionedPeriodicCNF.incidenceVertexPositionAt
        source placement (.clause data.indexed.1.clauseIndex))
  rw [← lookup]
  exact presentation.compatible.2.2.2.2.1 _
    (presentation.vertexPosition_mem member)

private theorem occurrenceLiteralIndex_eq_indexedLiteralIndex
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    occurrenceLiteralIndex source.erase entry.1.1 entry.1.2 =
      data.indexed.1.literalIndex := by
  let data := occurrenceSpliceData presentation entry
  calc
    occurrenceLiteralIndex source.erase entry.1.1 entry.1.2 =
        data.tagged.2.2 :=
      occurrenceLiteralIndex_of_occurrenceAt
        source.erase entry.1.1 entry.1.2
        data.tagged data.occurrenceLookup
    _ = data.indexed.1.literalIndex := by
      simpa [incidenceTaggedOccurrence] using
        congrArg (fun tagged => tagged.2.2) data.metadataEq.symm

private theorem occurrenceIndexedLiteralIndex_lt_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceSpliceData presentation entry).indexed.1.literalIndex < 3 := by
  let data := occurrenceSpliceData presentation entry
  change data.indexed.1.literalIndex < 3
  have incidenceMember :
      data.indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx data.indexedMember
  have members :=
    (PeriodicCNF.mem_incidencesWithMetadata_iff
      source.erase data.indexed.1).mp incidenceMember
  have literalLt :
      data.indexed.1.literalIndex <
        data.indexed.1.clause.length :=
    List.snd_lt_of_mem_zipIdx members.2
  have clauseWidth :
      data.indexed.1.clause.length ≤ 3 :=
    width data.indexed.1.clause
      (List.fst_mem_of_mem_zipIdx members.1)
  omega

private theorem terminalGroupOfLiteralIndex_injective_below_three
    {first second : Nat}
    (firstLt : first < 3)
    (secondLt : second < 3)
    (equal :
      terminalGroupOfLiteralIndex first =
        terminalGroupOfLiteralIndex second) :
    first = second := by
  interval_cases first <;> interval_cases second <;>
    simp [terminalGroupOfLiteralIndex] at equal ⊢

private theorem activeOccurrenceEntry_eq_of_indexedIncidence_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (incidenceEqual :
      (occurrenceSpliceData presentation first).indexed.1 =
        (occurrenceSpliceData presentation second).indexed.1) :
    first = second := by
  let firstData := occurrenceSpliceData presentation first
  let secondData := occurrenceSpliceData presentation second
  have taggedEqual : firstData.tagged = secondData.tagged := by
    calc
      firstData.tagged =
          incidenceTaggedOccurrence firstData.indexed.1 :=
        firstData.metadataEq.symm
      _ = incidenceTaggedOccurrence secondData.indexed.1 :=
        congrArg incidenceTaggedOccurrence incidenceEqual
      _ = secondData.tagged :=
        secondData.metadataEq
  have firstAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase first.1.1 first.1.2 firstData.tagged
      firstData.occurrenceLookup).2
  have secondAtom :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase second.1.1 second.1.2 secondData.tagged
      secondData.occurrenceLookup).2
  have atomEqual : first.1.1 = second.1.1 := by
    calc
      first.1.1 = firstData.tagged.1.atom := firstAtom.symm
      _ = secondData.tagged.1.atom :=
        congrArg (fun tagged => tagged.1.atom) taggedEqual
      _ = second.1.1 := secondAtom
  have firstLookup :
      occurrenceAt source.erase second.1.1 first.1.2 =
        some secondData.tagged := by
    simpa [atomEqual, taggedEqual] using
      firstData.occurrenceLookup
  have slotEqual : first.1.2 = second.1.2 :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_slot_unique
      source.erase second.1.1 secondData.tagged
      first.1.2 second.1.2
      firstLookup secondData.occurrenceLookup
  apply Subtype.ext
  exact Prod.ext atomEqual slotEqual

/-- Width at most three proves the terminal-group uniqueness contract used
by the source clause-fan adapter. -/
theorem sourceClauseTargetTerminalGroupsUnique_of_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3) :
    SourceClauseTargetTerminalGroupsUnique presentation := by
  intro target first second firstMember secondMember groupEqual
  let firstData := occurrenceSpliceData presentation first
  let secondData := occurrenceSpliceData presentation second
  let drawing :=
    PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes
  have targetsEqual :
      occurrenceSourceClauseTarget presentation first =
        occurrenceSourceClauseTarget presentation second :=
    ((mem_activeClauseTargetOccurrenceEntries_iff
      presentation target first).mp firstMember).trans
      ((mem_activeClauseTargetOccurrenceEntries_iff
        presentation target second).mp secondMember).symm
  have liftedEqual :
      Cell.add
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement
              (.clause firstData.indexed.1.clauseIndex))
          (drawing.periodTranslation
            (PositionedPeriodicCNF.variableToClauseTranslate
              firstData.indexed.1)) =
        Cell.add
          (PositionedPeriodicCNF.incidenceVertexPositionAt
            source placement
              (.clause secondData.indexed.1.clauseIndex))
          (drawing.periodTranslation
            (PositionedPeriodicCNF.variableToClauseTranslate
              secondData.indexed.1)) := by
    rw [← occurrenceSourceClauseTarget_eq_liftedClauseVertex
      presentation first,
      ← occurrenceSourceClauseTarget_eq_liftedClauseVertex
        presentation second]
    exact targetsEqual
  have baseEqual :=
    (PeriodicGridDrawing.translatedFundamentalPositions_eq
      drawing
      (occurrenceClauseVertex_in_fundamentalSquare
        presentation first)
      (occurrenceClauseVertex_in_fundamentalSquare
        presentation second)
      liftedEqual).1
  have firstClauseMember :
      CNFVertex.clause firstData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices :=
    occurrenceClauseVertex_member presentation first
  have secondClauseMember :
      CNFVertex.clause secondData.indexed.1.clauseIndex ∈
        source.erase.incidenceGraph.vertices :=
    occurrenceClauseVertex_member presentation second
  have baseEqual' :
      PositionedPeriodicCNF.incidenceVertexPositionAt
          source placement
            (.clause firstData.indexed.1.clauseIndex) =
        PositionedPeriodicCNF.incidenceVertexPositionAt
          source placement
            (.clause secondData.indexed.1.clauseIndex) := by
    simpa [firstData, secondData] using baseEqual
  have firstLookup :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes firstClauseMember
  have secondLookup :=
    PositionedPeriodicCNF.incidenceDrawing_vertexPosition_of_mem
      source placement presentation.routes secondClauseMember
  have clauseVertexEqual :
      (CNFVertex.clause firstData.indexed.1.clauseIndex :
          CNFVertex Variable) =
        CNFVertex.clause secondData.indexed.1.clauseIndex := by
    apply presentation.vertexPosition_injective_on
      firstClauseMember secondClauseMember
    rw [firstLookup, secondLookup]
    exact baseEqual'
  have clauseIndexEqual :
      firstData.indexed.1.clauseIndex =
        secondData.indexed.1.clauseIndex := by
    exact CNFVertex.clause.inj clauseVertexEqual
  have indexedGroupsEqual :
      terminalGroupOfLiteralIndex firstData.indexed.1.literalIndex =
        terminalGroupOfLiteralIndex secondData.indexed.1.literalIndex := by
    simpa [occurrenceClauseTerminalGroup,
      occurrenceLiteralIndex_eq_indexedLiteralIndex
        presentation first,
      occurrenceLiteralIndex_eq_indexedLiteralIndex
        presentation second] using groupEqual
  have literalIndexEqual :
      firstData.indexed.1.literalIndex =
        secondData.indexed.1.literalIndex :=
    terminalGroupOfLiteralIndex_injective_below_three
      (occurrenceIndexedLiteralIndex_lt_three
        presentation width first)
      (occurrenceIndexedLiteralIndex_lt_three
        presentation width second)
      indexedGroupsEqual
  have firstIncidenceMember :
      firstData.indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx firstData.indexedMember
  have secondIncidenceMember :
      secondData.indexed.1 ∈
        PeriodicCNF.incidencesWithMetadata source.erase :=
    List.fst_mem_of_mem_zipIdx secondData.indexedMember
  have incidenceEqual :
      firstData.indexed.1 = secondData.indexed.1 :=
    PeriodicCNF.incidence_eq_of_indices_eq source.erase
      firstIncidenceMember secondIncidenceMember
      clauseIndexEqual literalIndexEqual
  exact activeOccurrenceEntry_eq_of_indexedIncidence_eq
    presentation first second incidenceEqual

namespace ClauseRibbonFanData

/-- Width three directly supplies the exact source direction recorded for
an occurrence at a selected lifted clause target. -/
theorem sourceClauseRibbonFanData_direction_of_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (target : Cell)
    (entry : ActiveOccurrenceEntry source.erase)
    (member :
      entry ∈ activeClauseTargetOccurrenceEntries presentation target) :
    (sourceClauseRibbonFanData presentation target).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry :=
  sourceClauseRibbonFanData_direction presentation
    (sourceClauseTargetTerminalGroupsUnique_of_widthAtMostThree
      presentation width)
    target entry member

/-- Occurrence-specific convenience form of the width-three direction
lookup theorem. -/
theorem sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceClauseRibbonFanData presentation
        (occurrenceSourceClauseTarget presentation entry)).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry :=
  sourceClauseRibbonFanData_direction_at_occurrence presentation
    (sourceClauseTargetTerminalGroupsUnique_of_widthAtMostThree
      presentation width)
    entry

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
