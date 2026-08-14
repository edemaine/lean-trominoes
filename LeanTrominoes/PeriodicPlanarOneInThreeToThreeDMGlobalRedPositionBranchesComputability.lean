/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRedPositionTablesComputability

/-! # Primitive-recursive branches of assembled red-element positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

theorem assembledRedCyclePosition_primrec
    {Input Variable : Type*}
    [Primcodable Input] [Primcodable Variable]
    (variableOrigin : Input → Variable → Cell)
    (variableOriginPrimrec : Primrec fun input : Input × Variable =>
      variableOrigin input.1 input.2) :
    Primrec fun input : Input × (Variable × OccurrenceSlot) =>
      Cell.add (variableOrigin input.1 input.2.1)
        (cycleLinkPositionTable input.2.2) := by
  have origin : Primrec fun input : Input ×
      (Variable × OccurrenceSlot) =>
      variableOrigin input.1 input.2.1 :=
    variableOriginPrimrec.comp
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
  have localPosition : Primrec fun input : Input ×
      (Variable × OccurrenceSlot) =>
      cycleLinkPositionTable input.2.2 :=
    cycleLinkPositionTable_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  exact Computability.cell_add_primrec.comp origin localPosition

theorem assembledRedFixedPosition_primrec
    {Input Variable : Type*}
    [Primcodable Input] [Primcodable Variable] [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (variableOrigin : Input → Variable → Cell)
    (sourcePrimrec : Primrec source)
    (variableOriginPrimrec : Primrec fun input : Input × Variable =>
      variableOrigin input.1 input.2) :
    Primrec fun input : Input ×
        ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      Cell.add (variableOrigin input.1 input.2.1.1)
        (fixedRedInternalRedPositionTable
          ((input.2.1.2,
            occurrencePolarity (source input.1)
              input.2.1.1 input.2.1.2), input.2.2)) := by
  have atom : Primrec fun input : Input ×
      ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      input.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have slot : Primrec fun input : Input ×
      ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      input.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have origin : Primrec fun input : Input ×
      ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      variableOrigin input.1 input.2.1.1 :=
    variableOriginPrimrec.comp (Primrec.pair Primrec.fst atom)
  have polarity : Primrec fun input : Input ×
      ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      occurrencePolarity (source input.1)
        input.2.1.1 input.2.1.2 :=
    occurrencePolarity_primrec.comp
      (Primrec.pair
        (Primrec.pair (sourcePrimrec.comp Primrec.fst) atom) slot)
  have localPosition : Primrec fun input : Input ×
      ((Variable × OccurrenceSlot) × FixedRedInternalRed) =>
      fixedRedInternalRedPositionTable
        ((input.2.1.2,
          occurrencePolarity (source input.1)
            input.2.1.1 input.2.1.2), input.2.2) :=
    fixedRedInternalRedPositionTable_primrec.comp
      (Primrec.pair (Primrec.pair slot polarity)
        (Primrec.snd.comp Primrec.snd))
  exact Computability.cell_add_primrec.comp origin localPosition

theorem assembledRedClausePosition_primrec
    {Input : Type*} [Primcodable Input]
    (clauseOrigin : Input → Nat → Cell)
    (clauseOriginPrimrec : Primrec fun input : Input × Nat =>
      clauseOrigin input.1 input.2) :
    Primrec fun input : Input ×
        Sum Nat (Nat × X3CClauseTerminalGroup) =>
      match input.2 with
      | .inl clauseIndex =>
          Cell.add (clauseOrigin input.1 clauseIndex)
            redClauseInternalPosition
      | .inr data =>
          Cell.add (clauseOrigin input.1 data.1)
            (redClauseTerminalPositionTable data.2) := by
  let ClauseData := Sum Nat (Nat × X3CClauseTerminalGroup)
  let Query := Input × ClauseData
  have internalCase : Primrec₂ fun (input : Query) (clauseIndex : Nat) =>
      Cell.add (clauseOrigin input.1 clauseIndex)
        redClauseInternalPosition := by
    change Primrec fun data : Query × Nat =>
      Cell.add (clauseOrigin data.1.1 data.2)
        redClauseInternalPosition
    have origin : Primrec fun data : Query × Nat =>
        clauseOrigin data.1.1 data.2 :=
      clauseOriginPrimrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    exact Computability.cell_add_primrec.comp origin
      (Primrec.const redClauseInternalPosition)
  have terminalCase : Primrec₂ fun (input : Query)
      (data : Nat × X3CClauseTerminalGroup) =>
      Cell.add (clauseOrigin input.1 data.1)
        (redClauseTerminalPositionTable data.2) := by
    change Primrec fun combined : Query ×
        (Nat × X3CClauseTerminalGroup) =>
      Cell.add (clauseOrigin combined.1.1 combined.2.1)
        (redClauseTerminalPositionTable combined.2.2)
    have origin : Primrec fun combined : Query ×
        (Nat × X3CClauseTerminalGroup) =>
        clauseOrigin combined.1.1 combined.2.1 :=
      clauseOriginPrimrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
    have localPosition : Primrec fun combined : Query ×
        (Nat × X3CClauseTerminalGroup) =>
        redClauseTerminalPositionTable combined.2.2 :=
      redClauseTerminalPositionTable_primrec.comp
        (Primrec.snd.comp Primrec.snd)
    exact Computability.cell_add_primrec.comp origin localPosition
  exact (Primrec.sumCasesOn Primrec.snd internalCase terminalCase).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
