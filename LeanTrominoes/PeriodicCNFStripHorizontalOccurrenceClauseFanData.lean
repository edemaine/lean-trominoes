/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMAxisDirectionEquivalence

/-! # Executable clause-fan data for horizontal occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A concrete strip source paired with one normalized clause-orbit index. -/
abbrev HorizontalClauseRibbonFanInput := PeriodicCNF Nat × Nat

/-- Proof-erased occurrence entry used by the executable clause fan. -/
abbrev HorizontalClauseOccurrenceEntry := RoutedVariable × OccurrenceSlot

/-- One clause-fan query for a finite terminal group. -/
abbrev HorizontalClauseRibbonGroupInput :=
  HorizontalClauseRibbonFanInput × X3CClauseTerminalGroup

/-- Canonical finite code of one clause-fan record. -/
abbrev HorizontalClauseRibbonFanCode :=
  Bool × (Fin 5 × Fin 5 × Fin 5)

/-- Exact normalized source read by the proof-free clause-fan builder. -/
def horizontalOccurrenceClauseSourceComputed
    (input : HorizontalClauseRibbonFanInput) : PeriodicCNF RoutedVariable :=
  (horizontalNormalizedRoutedFormulaComputed input.1).erase

/-- Repackage a proof-erased clause entry as the normalized occurrence-table
query. -/
def horizontalOccurrenceClauseEntryQueryComputed
    (input : HorizontalClauseRibbonFanInput ×
      HorizontalClauseOccurrenceEntry) : HorizontalOccurrenceRouteInput :=
  ((input.1.1, input.2.1), input.2.2)

/-- Tagged normalized source occurrence stored at one proof-erased entry. -/
def horizontalOccurrenceClauseEntryLookupComputed
    (input : HorizontalClauseRibbonFanInput ×
      HorizontalClauseOccurrenceEntry) :
    Option (TaggedOccurrence RoutedVariable) :=
  horizontalOccurrenceLookupComputed
    (horizontalOccurrenceClauseEntryQueryComputed input)

/-- Stored normalized clause index of one proof-erased entry. -/
def horizontalOccurrenceClauseEntryClauseIndexComputed
    (input : HorizontalClauseRibbonFanInput ×
      HorizontalClauseOccurrenceEntry) : Nat :=
  match horizontalOccurrenceClauseEntryLookupComputed input with
  | none => 0
  | some tagged => tagged.2.1

/-- Stored normalized literal index of one proof-erased entry. -/
def horizontalOccurrenceClauseEntryLiteralIndexComputed
    (input : HorizontalClauseRibbonFanInput ×
      HorizontalClauseOccurrenceEntry) : Nat :=
  match horizontalOccurrenceClauseEntryLookupComputed input with
  | none => 0
  | some tagged => tagged.2.2

/-- Proof-erased active occurrences belonging to one normalized clause
orbit. -/
def horizontalOccurrenceClauseEntriesComputed
    (input : HorizontalClauseRibbonFanInput) :
    List HorizontalClauseOccurrenceEntry :=
  (occurrenceEntries
    (horizontalOccurrenceClauseSourceComputed input)).filterMap fun entry =>
      if horizontalOccurrenceClauseEntryClauseIndexComputed
          (input, entry) = input.2 then
        some entry
      else
        none

/-- Terminal group occupied by one proof-erased clause occurrence. -/
def horizontalOccurrenceClauseEntryGroupComputed
    (input : HorizontalClauseRibbonFanInput ×
      HorizontalClauseOccurrenceEntry) : X3CClauseTerminalGroup :=
  terminalGroupOfLiteralIndex
    (horizontalOccurrenceClauseEntryLiteralIndexComputed input)

/-- Whether one proof-erased entry occupies the requested terminal group. -/
def horizontalOccurrenceClauseEntryMatchesGroupComputed
    (input : HorizontalClauseRibbonGroupInput ×
      HorizontalClauseOccurrenceEntry) : Bool :=
  decide
    (horizontalOccurrenceClauseEntryGroupComputed
      (input.1.1, input.2) = input.1.2)

/-- First occurrence in a clause orbit occupying the requested terminal
group. -/
def horizontalOccurrenceClauseSelectedEntryComputed
    (input : HorizontalClauseRibbonGroupInput) :
    Option HorizontalClauseOccurrenceEntry :=
  (horizontalOccurrenceClauseEntriesComputed input.1).find? fun entry =>
    horizontalOccurrenceClauseEntryMatchesGroupComputed (input, entry)

/-- Whether the normalized clause has a right terminal. -/
def horizontalOccurrenceClauseHasRightComputed
    (input : HorizontalClauseRibbonFanInput) : Bool :=
  (horizontalOccurrenceClauseSelectedEntryComputed (input, .right)).isSome

/-- Incoming source-route direction stored for one clause terminal group. -/
def horizontalOccurrenceClauseDirectionComputed
    (input : HorizontalClauseRibbonFanInput)
    (group : X3CClauseTerminalGroup) : AxisDirection :=
  match horizontalOccurrenceClauseSelectedEntryComputed (input, group) with
  | none => .north
  | some entry =>
      horizontalOccurrenceSourceClauseDirectionComputed
        ((input.1, entry.1), entry.2)

/-- List of the three encoded clause-fan directions. -/
def horizontalOccurrenceClauseDirectionCodesListComputed
    (input : HorizontalClauseRibbonFanInput) : List (Fin 5) :=
  ([.top, .left, .right] : List X3CClauseTerminalGroup).map fun group =>
    axisDirectionEquivFin
      (horizontalOccurrenceClauseDirectionComputed input group)

/-- Convert a clause direction-code list to its three-field code. -/
def horizontalOccurrenceClauseDirectionCodesTriple
    (codes : List (Fin 5)) : Fin 5 × Fin 5 × Fin 5 :=
  (codes.getD 0 0, codes.getD 1 0, codes.getD 2 0)

/-- Complete finite code of one proof-free clause fan. -/
def horizontalOccurrenceClauseRibbonFanCodeComputed
    (input : HorizontalClauseRibbonFanInput) :
    HorizontalClauseRibbonFanCode :=
  (horizontalOccurrenceClauseHasRightComputed input,
    horizontalOccurrenceClauseDirectionCodesTriple
      (horizontalOccurrenceClauseDirectionCodesListComputed input))

/-- Decode the canonical finite clause-fan code. -/
def horizontalOccurrenceClauseRibbonFanDataOfCode
    (code : HorizontalClauseRibbonFanCode) : ClauseRibbonFanData where
  hasRight := code.1
  direction
    | .top => axisDirectionEquivFin.symm code.2.1
    | .left => axisDirectionEquivFin.symm code.2.2.1
    | .right => axisDirectionEquivFin.symm code.2.2.2

/-- Complete proof-free clause-fan record for one normalized clause orbit. -/
def horizontalOccurrenceClauseRibbonFanDataComputed
    (input : HorizontalClauseRibbonFanInput) : ClauseRibbonFanData :=
  horizontalOccurrenceClauseRibbonFanDataOfCode
    (horizontalOccurrenceClauseRibbonFanCodeComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
