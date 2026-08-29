/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordSlotAttachment
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleCompiler

/-! # Grouping final occurrence-role/slot pairs by copied clause -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open PeriodicEightOccurrenceSplit

abbrev Query := RetainedFinalCopiedClauseQuery
abbrev Slot := RetainedTerminalSlot
abbrev Input := RetainedFinalCopiedClauseOccurrenceRole × Slot
abbrev Output := RetainedDirectClauseRouteTailRecordSlotInput

/-- `none` is between queries.  A present state stores its query, first slot,
and optionally its second slot while a binary or ternary query is open. -/
abbrev Control := Option (Query × Slot × Option Slot)

/-- Local opaque wrapper preventing unrelated descriptor simplification from
expanding the small control decision. -/
def queryArity (query : Query) : Nat :=
  retainedFinalCopiedClauseQueryArity query

def transition (control : Control) (input : Input) :
    Control × List Output :=
  let query := input.1.1
  let literalIndex := input.1.2.val
  let slot := input.2
  match queryArity query, literalIndex with
  | 1, 0 =>
      (none, [(query, .unary slot)])
  | 2, 0 =>
      (some (query, slot, none), [])
  | 2, 1 =>
      match control with
      | some (savedQuery, first, none) =>
          if savedQuery = query then
            (none, [(query, .binary first slot)])
          else
            (none, [])
      | _ => (none, [])
  | 3, 0 =>
      (some (query, slot, none), [])
  | 3, 1 =>
      match control with
      | some (savedQuery, first, none) =>
          if savedQuery = query then
            (some (query, first, some slot), [])
          else
            (none, [])
      | _ => (none, [])
  | 3, 2 =>
      match control with
      | some (savedQuery, first, some second) =>
          if savedQuery = query then
            (none, [(query, .ternary first second slot)])
          else
            (none, [])
      | _ => (none, [])
  | _, _ => (none, [])

def finish (_ : Control) : List Output := []

def slotInputs (inputs : List Input) : List Output :=
  FiniteStateTransducer.output none transition finish inputs

/-- Declarative left-to-right grouping of a query list against one flat slot
stream.  The compiled transducer below is proved equal to this specification
when the slot count matches the query occurrence count. -/
def slotInputsOfQueries : List Query → List Slot → List Output
  | [], _ => []
  | query :: queries, slots =>
      match queryArity query, slots with
      | 0, _ => slotInputsOfQueries queries slots
      | 1, first :: rest =>
          (query, .unary first) :: slotInputsOfQueries queries rest
      | 2, first :: second :: rest =>
          (query, .binary first second) ::
            slotInputsOfQueries queries rest
      | 3, first :: second :: third :: rest =>
          (query, .ternary first second third) ::
            slotInputsOfQueries queries rest
      | _, _ => []

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end
