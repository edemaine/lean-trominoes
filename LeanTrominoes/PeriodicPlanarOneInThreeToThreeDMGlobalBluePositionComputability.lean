/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalBluePositionBranchesComputability

/-! # Computability of data-only assembled blue-element positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

theorem assembledBlueElementPositionData_primrec
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
    Primrec fun input : Input × BlueElement Variable =>
      assembledBlueElementPositionData (source input.1)
        (variableOrigin input.1) (clauseOrigin input.1) input.2 := by
  let OrdinaryData :=
    (Variable × OccurrenceSlot) × OrdinaryInternal
  let FixedData :=
    (Variable × OccurrenceSlot) × FixedRedInternalBlue
  let ClauseData := Sum Nat (Nat × X3CClauseTerminalGroup)
  let Query := Input × BlueElement Variable
  have encoded : Primrec fun input : Query => blueElementEquivData input.2 :=
    (Primrec.of_equiv : Primrec (@blueElementEquivData Variable)).comp
      Primrec.snd
  have ordinaryCase : Primrec₂ fun (input : Query)
      (ordinary : OrdinaryData) =>
      Cell.add (variableOrigin input.1 ordinary.1.1)
        (ordinaryInternalPositionTable
          (((ordinary.1.2,
            occurrenceConnectorKind (source input.1)
              ordinary.1.1 ordinary.1.2),
            occurrencePolarity (source input.1)
              ordinary.1.1 ordinary.1.2), ordinary.2)) := by
    change Primrec fun combined : Query × OrdinaryData =>
      Cell.add (variableOrigin combined.1.1 combined.2.1.1)
        (ordinaryInternalPositionTable
          (((combined.2.1.2,
            occurrenceConnectorKind (source combined.1.1)
              combined.2.1.1 combined.2.1.2),
            occurrencePolarity (source combined.1.1)
              combined.2.1.1 combined.2.1.2), combined.2.2))
    exact
      (assembledOrdinaryInternalPosition_primrec source variableOrigin
        sourcePrimrec variableOriginPrimrec).comp
          (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have restCase : Primrec₂ fun (input : Query)
      (rest : Sum FixedData ClauseData) =>
      match rest with
      | .inl fixed =>
          Cell.add (variableOrigin input.1 fixed.1.1)
            (fixedRedInternalBluePositionTable
              ((fixed.1.2,
                occurrencePolarity (source input.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          match clause with
          | .inl clauseIndex =>
              Cell.add (clauseOrigin input.1 clauseIndex)
                blueClauseInternalPosition
          | .inr data =>
              Cell.add (clauseOrigin input.1 data.1)
                (blueClauseTerminalPositionTable data.2) := by
    change Primrec fun combined : Query × Sum FixedData ClauseData =>
      match combined.2 with
      | .inl fixed =>
          Cell.add (variableOrigin combined.1.1 fixed.1.1)
            (fixedRedInternalBluePositionTable
              ((fixed.1.2,
                occurrencePolarity (source combined.1.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          match clause with
          | .inl clauseIndex =>
              Cell.add (clauseOrigin combined.1.1 clauseIndex)
                blueClauseInternalPosition
          | .inr data =>
              Cell.add (clauseOrigin combined.1.1 data.1)
                (blueClauseTerminalPositionTable data.2)
    have fixedCase : Primrec₂ fun
        (combined : Query × Sum FixedData ClauseData)
        (fixed : FixedData) =>
        Cell.add (variableOrigin combined.1.1 fixed.1.1)
          (fixedRedInternalBluePositionTable
            ((fixed.1.2,
              occurrencePolarity (source combined.1.1)
                fixed.1.1 fixed.1.2), fixed.2)) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
        Cell.add (variableOrigin data.1.1.1 data.2.1.1)
          (fixedRedInternalBluePositionTable
            ((data.2.1.2,
              occurrencePolarity (source data.1.1.1)
                data.2.1.1 data.2.1.2), data.2.2))
      exact
        (assembledBlueFixedPosition_primrec source variableOrigin
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
              blueClauseInternalPosition
        | .inr data =>
            Cell.add (clauseOrigin combined.1.1 data.1)
              (blueClauseTerminalPositionTable data.2) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × ClauseData =>
        match data.2 with
        | .inl clauseIndex =>
            Cell.add (clauseOrigin data.1.1.1 clauseIndex)
              blueClauseInternalPosition
        | .inr terminal =>
            Cell.add (clauseOrigin data.1.1.1 terminal.1)
              (blueClauseTerminalPositionTable terminal.2)
      exact
        (assembledBlueClausePosition_primrec
          clauseOrigin clauseOriginPrimrec).comp
            (Primrec.pair
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              Primrec.snd)
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded ordinaryCase restCase).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
