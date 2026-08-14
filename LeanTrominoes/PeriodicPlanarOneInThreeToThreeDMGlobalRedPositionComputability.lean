/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRedPositionBranchesComputability

/-! # Computability of data-only assembled red-element positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

theorem assembledRedElementPositionData_primrec
    {Input Variable : Type*}
    [Primcodable Input] [Primcodable Variable] [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (variableOrigin : Input → Variable → Cell)
    (clauseOrigin : Input → Nat → Cell)
    (sourcePrimrec : Primrec source)
    (variableOriginPrimrec : Primrec fun input : Input × Variable =>
      variableOrigin input.1 input.2)
    (clauseOriginPrimrec : Primrec fun input : Input × Nat =>
      clauseOrigin input.1 input.2) :
    Primrec fun input : Input × RedElement Variable =>
      assembledRedElementPositionData (source input.1)
        (variableOrigin input.1) (clauseOrigin input.1) input.2 := by
  let CycleData := Variable × OccurrenceSlot
  let FixedData :=
    (Variable × OccurrenceSlot) × FixedRedInternalRed
  let ClauseData := Sum Nat (Nat × X3CClauseTerminalGroup)
  let Query := Input × RedElement Variable
  have encoded : Primrec fun input : Query => redElementEquivData input.2 :=
    (Primrec.of_equiv : Primrec (@redElementEquivData Variable)).comp
      Primrec.snd
  have cycleCase : Primrec₂ fun (input : Query) (cycle : CycleData) =>
      Cell.add (variableOrigin input.1 cycle.1)
        (cycleLinkPositionTable cycle.2) := by
    change Primrec fun combined : Query × CycleData =>
      Cell.add (variableOrigin combined.1.1 combined.2.1)
        (cycleLinkPositionTable combined.2.2)
    exact
      (assembledRedCyclePosition_primrec
        variableOrigin variableOriginPrimrec).comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have restCase : Primrec₂ fun (input : Query)
      (rest : Sum FixedData ClauseData) =>
      match rest with
      | .inl fixed =>
          Cell.add (variableOrigin input.1 fixed.1.1)
            (fixedRedInternalRedPositionTable
              ((fixed.1.2,
                occurrencePolarity (source input.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          match clause with
          | .inl clauseIndex =>
              Cell.add (clauseOrigin input.1 clauseIndex)
                redClauseInternalPosition
          | .inr data =>
              Cell.add (clauseOrigin input.1 data.1)
                (redClauseTerminalPositionTable data.2) := by
    change Primrec fun combined : Query × Sum FixedData ClauseData =>
      match combined.2 with
      | .inl fixed =>
          Cell.add (variableOrigin combined.1.1 fixed.1.1)
            (fixedRedInternalRedPositionTable
              ((fixed.1.2,
                occurrencePolarity (source combined.1.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          match clause with
          | .inl clauseIndex =>
              Cell.add (clauseOrigin combined.1.1 clauseIndex)
                redClauseInternalPosition
          | .inr data =>
              Cell.add (clauseOrigin combined.1.1 data.1)
                (redClauseTerminalPositionTable data.2)
    have fixedCase : Primrec₂ fun
        (combined : Query × Sum FixedData ClauseData)
        (fixed : FixedData) =>
        Cell.add (variableOrigin combined.1.1 fixed.1.1)
          (fixedRedInternalRedPositionTable
            ((fixed.1.2,
              occurrencePolarity (source combined.1.1)
                fixed.1.1 fixed.1.2), fixed.2)) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
        Cell.add (variableOrigin data.1.1.1 data.2.1.1)
          (fixedRedInternalRedPositionTable
            ((data.2.1.2,
              occurrencePolarity (source data.1.1.1)
                data.2.1.1 data.2.1.2), data.2.2))
      exact
        (assembledRedFixedPosition_primrec source variableOrigin
          sourcePrimrec variableOriginPrimrec).comp
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              Primrec.snd)
    have clauseCase : Primrec₂ fun
        (combined : Query × Sum FixedData ClauseData)
        (clause : ClauseData) =>
        match clause with
        | .inl clauseIndex =>
            Cell.add (clauseOrigin combined.1.1 clauseIndex)
              redClauseInternalPosition
        | .inr data =>
            Cell.add (clauseOrigin combined.1.1 data.1)
              (redClauseTerminalPositionTable data.2) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × ClauseData =>
        match data.2 with
        | .inl clauseIndex =>
            Cell.add (clauseOrigin data.1.1.1 clauseIndex)
              redClauseInternalPosition
        | .inr terminal =>
            Cell.add (clauseOrigin data.1.1.1 terminal.1)
              (redClauseTerminalPositionTable terminal.2)
      exact
        (assembledRedClausePosition_primrec
          clauseOrigin clauseOriginPrimrec).comp
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              Primrec.snd)
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded cycleCase restCase).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
