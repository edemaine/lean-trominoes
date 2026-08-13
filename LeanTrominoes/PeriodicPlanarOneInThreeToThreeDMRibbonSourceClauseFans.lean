/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirectionFamilies

/-!
# Source clause-orbit data for coordinated ribbon fans

The finite clause-fan tables are indexed by a `ClauseRibbonFanData`.  This
file constructs that record from all active source occurrences belonging to
one finite clause orbit.

The construction detects whether the right terminal is present and looks up
the genuine incoming direction belonging to each terminal group.  Correctness
of the direction lookup uses the precise source-side condition still needed
at this boundary: in one clause orbit, at most one active occurrence may
occupy each terminal group.  The resulting fan is translated independently
to every physical copy of the clause, which correctly handles nonzero literal
offsets.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Clause-terminal group occupied by one active source occurrence. -/
def occurrenceClauseTerminalGroup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (entry : ActiveOccurrenceEntry source) :
    X3CClauseTerminalGroup :=
  terminalGroupOfLiteralIndex
    (occurrenceLiteralIndex source entry.1.1 entry.1.2)

/-- No two distinct source occurrences belonging to one clause orbit occupy
the same clause-terminal group. -/
def SourceClauseTerminalGroupsUnique
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (_presentation : source.PlanarIncidencePresentation placement) : Prop :=
  ∀ clauseIndex first second,
    first ∈ activeClauseOccurrenceEntries source.erase clauseIndex →
    second ∈ activeClauseOccurrenceEntries source.erase clauseIndex →
    occurrenceClauseTerminalGroup source.erase first =
        occurrenceClauseTerminalGroup source.erase second →
    first = second

/-- Finite coordinated-fan data read from one source clause orbit.

The north fallback is observed only for an inactive terminal group. -/
noncomputable def sourceClauseRibbonFanData
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (clauseIndex : Nat) :
    ClauseRibbonFanData :=
  let entries :=
    activeClauseOccurrenceEntries source.erase clauseIndex
  {
    hasRight :=
      entries.any fun entry =>
        decide
          (occurrenceClauseTerminalGroup source.erase entry = .right)
    direction := fun group =>
      match entries.find? fun entry =>
          decide
            (occurrenceClauseTerminalGroup source.erase entry = group) with
      | some entry =>
          occurrenceSourceClauseDirection presentation entry
      | none => .north
  }

private theorem find?_eq_some_of_mem_of_unique
    {α : Type*}
    (values : List α)
    (predicate : α → Bool)
    (selected : α)
    (member : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (unique :
      ∀ candidate ∈ values,
        predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      by_cases headTrue : predicate head = true
      · have headEq : head = selected :=
          unique head (by simp) headTrue
        subst head
        simp [selectedTrue]
      · have selectedTail : selected ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with selectedEq | selectedTail
          · subst head
            exact (headTrue selectedTrue).elim
          · exact selectedTail
        have tailUnique :
            ∀ candidate ∈ tail,
              predicate candidate = true →
                candidate = selected := by
          intro candidate candidateMember candidateTrue
          exact unique candidate (by simp [candidateMember]) candidateTrue
        simp [headTrue, induction selectedTail tailUnique]

namespace ClauseRibbonFanData

/-- The source record activates the right terminal exactly when some source
occurrence in the selected clause orbit occupies it. -/
theorem sourceClauseRibbonFanData_hasRight_iff
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (clauseIndex : Nat) :
    (sourceClauseRibbonFanData presentation clauseIndex).hasRight = true ↔
      ∃ entry ∈
          activeClauseOccurrenceEntries source.erase clauseIndex,
        occurrenceClauseTerminalGroup source.erase entry = .right := by
  simp [sourceClauseRibbonFanData]

/-- Every actual source occurrence in the selected clause orbit occupies an
active terminal group of the resulting finite fan. -/
theorem sourceClauseRibbonFanData_groupActive
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (clauseIndex : Nat)
    (entry : ActiveOccurrenceEntry source.erase)
    (member :
      entry ∈ activeClauseOccurrenceEntries
        source.erase clauseIndex) :
    (sourceClauseRibbonFanData presentation clauseIndex).GroupActive
      (occurrenceClauseTerminalGroup source.erase entry) := by
  cases groupEq :
      occurrenceClauseTerminalGroup source.erase entry with
  | top =>
      unfold GroupActive activeGroups
      split <;> simp
  | left =>
      unfold GroupActive activeGroups
      split <;> simp
  | right =>
      have hasRight :
          (sourceClauseRibbonFanData presentation clauseIndex).hasRight =
            true := by
        rw [sourceClauseRibbonFanData_hasRight_iff]
        exact ⟨entry, member, groupEq⟩
      simp [GroupActive, activeGroups, hasRight]

/-- Under terminal-group uniqueness, the finite fan records the genuine
incoming direction of every occurrence in its clause orbit. -/
theorem sourceClauseRibbonFanData_direction
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (groupsUnique :
      SourceClauseTerminalGroupsUnique presentation)
    (clauseIndex : Nat)
    (entry : ActiveOccurrenceEntry source.erase)
    (member :
      entry ∈ activeClauseOccurrenceEntries
        source.erase clauseIndex) :
    (sourceClauseRibbonFanData presentation clauseIndex).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry := by
  let entries :=
    activeClauseOccurrenceEntries source.erase clauseIndex
  let group :=
    occurrenceClauseTerminalGroup source.erase entry
  let predicate := fun candidate : ActiveOccurrenceEntry source.erase =>
    decide
      (occurrenceClauseTerminalGroup source.erase candidate = group)
  have selectedTrue : predicate entry = true := by
    simp [predicate, group]
  have unique :
      ∀ candidate ∈ entries,
        predicate candidate = true → candidate = entry := by
    intro candidate candidateMember candidateTrue
    apply groupsUnique clauseIndex candidate entry candidateMember member
    simpa [predicate, group] using of_decide_eq_true candidateTrue
  have found :
      entries.find? predicate = some entry :=
    find?_eq_some_of_mem_of_unique
      entries predicate entry member selectedTrue unique
  simp [sourceClauseRibbonFanData, entries, predicate, group, found]

/-- The occurrence-specific form uses the clause orbit selected by that same
occurrence. -/
theorem sourceClauseRibbonFanData_direction_at_occurrence
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (groupsUnique :
      SourceClauseTerminalGroupsUnique presentation)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceClauseRibbonFanData presentation
        (occurrenceClauseIndex source.erase
          entry.1.1 entry.1.2)).direction
        (occurrenceClauseTerminalGroup source.erase entry) =
      occurrenceSourceClauseDirection presentation entry :=
  sourceClauseRibbonFanData_direction presentation groupsUnique
    (occurrenceClauseIndex source.erase
      entry.1.1 entry.1.2) entry
    entry.mem_activeClauseOccurrenceEntries

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
