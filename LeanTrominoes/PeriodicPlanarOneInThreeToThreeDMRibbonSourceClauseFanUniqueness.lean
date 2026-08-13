/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans

/-!
# Uniqueness of clause-orbit fan terminal groups

The source clause-fan adapter looks up one incoming direction for each of
the top, left, and right terminal groups.  This file proves that lookup is
unambiguous for every width-three positioned periodic CNF presentation.

Membership in one clause-orbit family already identifies the clause index.
Width at most three makes the terminal group identify the literal index,
and the existing occurrence-slot uniqueness theorem then identifies the
active source entries.  No equality between base routes' absolute clause
targets is assumed: different literal offsets are handled by translating
one common clause-orbit fan.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The occurrence-table literal index agrees with the selected
metadata-rich incidence index. -/
theorem occurrenceLiteralIndex_eq_indexedLiteralIndex
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

/-- Width at most three proves the clause-orbit terminal-group uniqueness
contract used by the source clause-fan adapter. -/
theorem sourceClauseTerminalGroupsUnique_of_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3) :
    SourceClauseTerminalGroupsUnique presentation := by
  intro clauseIndex first second firstMember secondMember groupEqual
  let firstData := occurrenceSpliceData presentation first
  let secondData := occurrenceSpliceData presentation second
  have clauseIndexEqual :
      firstData.indexed.1.clauseIndex =
        secondData.indexed.1.clauseIndex := by
    calc
      firstData.indexed.1.clauseIndex =
          occurrenceClauseIndex source.erase
            first.1.1 first.1.2 :=
        (occurrenceClauseIndex_eq_indexedClauseIndex
          presentation first).symm
      _ = clauseIndex :=
        (mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex first).mp firstMember
      _ = occurrenceClauseIndex source.erase
            second.1.1 second.1.2 :=
        ((mem_activeClauseOccurrenceEntries_iff
          source.erase clauseIndex second).mp secondMember).symm
      _ = secondData.indexed.1.clauseIndex :=
        occurrenceClauseIndex_eq_indexedClauseIndex
          presentation second
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
an occurrence in a selected clause orbit. -/
theorem sourceClauseRibbonFanData_direction_of_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (clauseIndex : Nat)
    (entry : ActiveOccurrenceEntry source.erase)
    (member :
      entry ∈ activeClauseOccurrenceEntries
        source.erase clauseIndex) :
    (sourceClauseRibbonFanData presentation clauseIndex).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry :=
  sourceClauseRibbonFanData_direction presentation
    (sourceClauseTerminalGroupsUnique_of_widthAtMostThree
      presentation width)
    clauseIndex entry member

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
        (occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2)).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry :=
  sourceClauseRibbonFanData_direction_at_occurrence presentation
    (sourceClauseTerminalGroupsUnique_of_widthAtMostThree
      presentation width)
    entry

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
