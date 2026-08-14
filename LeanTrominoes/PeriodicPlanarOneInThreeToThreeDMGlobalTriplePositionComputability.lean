/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalTriplePositionTablesComputability

/-! # Computability of data-only assembled triple positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

theorem assembledTriplePositionData_primrec
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
    Primrec fun input : Input × Triple Variable =>
      assembledTriplePositionData (source input.1)
        (variableOrigin input.1) (clauseOrigin input.1) input.2 := by
  let OrdinaryData :=
    ((Variable × OccurrenceSlot) × VariableOccurrenceVariant) ×
      VariableOccurrenceTriple
  let FixedData :=
    (Variable × OccurrenceSlot) × FixedRedConnectorTriple
  let ClauseData := Nat × X3CClauseSet
  let Query := Input × Triple Variable
  have encoded : Primrec fun input : Query => tripleEquivData input.2 :=
    (Primrec.of_equiv : Primrec (@tripleEquivData Variable)).comp
      Primrec.snd
  have ordinaryCase : Primrec₂ fun (input : Query)
      (ordinary : OrdinaryData) =>
      Cell.add (variableOrigin input.1 ordinary.1.1.1)
        (ordinaryTripleSitePositionTable
          (((ordinary.1.1.2, ordinary.1.2),
            occurrencePolarity (source input.1)
              ordinary.1.1.1 ordinary.1.1.2), ordinary.2)) := by
    change Primrec fun combined : Query × OrdinaryData =>
      Cell.add (variableOrigin combined.1.1 combined.2.1.1.1)
        (ordinaryTripleSitePositionTable
          (((combined.2.1.1.2, combined.2.1.2),
            occurrencePolarity (source combined.1.1)
              combined.2.1.1.1 combined.2.1.1.2), combined.2.2))
    have atom : Primrec fun combined : Query × OrdinaryData =>
        combined.2.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd))
    have slot : Primrec fun combined : Query × OrdinaryData =>
        combined.2.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp
        (Primrec.fst.comp Primrec.snd))
    have variant : Primrec fun combined : Query × OrdinaryData =>
        combined.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have localTriple : Primrec fun combined : Query × OrdinaryData =>
        combined.2.2 :=
      Primrec.snd.comp Primrec.snd
    have origin : Primrec fun combined : Query × OrdinaryData =>
        variableOrigin combined.1.1 combined.2.1.1.1 :=
      variableOriginPrimrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) atom)
    have polarity : Primrec fun combined : Query × OrdinaryData =>
        occurrencePolarity (source combined.1.1)
          combined.2.1.1.1 combined.2.1.1.2 :=
      occurrencePolarity_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)) atom)
          slot)
    have localPosition : Primrec fun combined : Query × OrdinaryData =>
        ordinaryTripleSitePositionTable
          (((combined.2.1.1.2, combined.2.1.2),
            occurrencePolarity (source combined.1.1)
              combined.2.1.1.1 combined.2.1.1.2), combined.2.2) :=
      ordinaryTripleSitePositionTable_primrec.comp
        (Primrec.pair
          (Primrec.pair (Primrec.pair slot variant) polarity)
          localTriple)
    exact Computability.cell_add_primrec.comp origin localPosition
  have restCase : Primrec₂ fun (input : Query)
      (rest : Sum FixedData ClauseData) =>
      match rest with
      | .inl fixed =>
          Cell.add (variableOrigin input.1 fixed.1.1)
            (fixedRedTripleSitePositionTable
              ((fixed.1.2,
                occurrencePolarity (source input.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          Cell.add (clauseOrigin input.1 clause.1)
            (clauseTriplePositionTable clause.2) := by
    change Primrec fun combined : Query × Sum FixedData ClauseData =>
      match combined.2 with
      | .inl fixed =>
          Cell.add (variableOrigin combined.1.1 fixed.1.1)
            (fixedRedTripleSitePositionTable
              ((fixed.1.2,
                occurrencePolarity (source combined.1.1)
                  fixed.1.1 fixed.1.2), fixed.2))
      | .inr clause =>
          Cell.add (clauseOrigin combined.1.1 clause.1)
            (clauseTriplePositionTable clause.2)
    have fixedCase : Primrec₂ fun
        (combined : Query × Sum FixedData ClauseData)
        (fixed : FixedData) =>
        Cell.add (variableOrigin combined.1.1 fixed.1.1)
          (fixedRedTripleSitePositionTable
            ((fixed.1.2,
              occurrencePolarity (source combined.1.1)
                fixed.1.1 fixed.1.2), fixed.2)) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
        Cell.add (variableOrigin data.1.1.1 data.2.1.1)
          (fixedRedTripleSitePositionTable
            ((data.2.1.2,
              occurrencePolarity (source data.1.1.1)
                data.2.1.1 data.2.1.2), data.2.2))
      have atom : Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
          data.2.1.1 :=
        Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
      have slot : Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
          data.2.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
      have origin : Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
          variableOrigin data.1.1.1 data.2.1.1 :=
        variableOriginPrimrec.comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) atom)
      have polarity : Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
          occurrencePolarity (source data.1.1.1)
            data.2.1.1 data.2.1.2 :=
        occurrencePolarity_primrec.comp
          (Primrec.pair
            (Primrec.pair
              (sourcePrimrec.comp
                (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) atom)
            slot)
      have localPosition : Primrec fun data :
          (Query × Sum FixedData ClauseData) × FixedData =>
          fixedRedTripleSitePositionTable
            ((data.2.1.2,
              occurrencePolarity (source data.1.1.1)
                data.2.1.1 data.2.1.2), data.2.2) :=
        fixedRedTripleSitePositionTable_primrec.comp
          (Primrec.pair (Primrec.pair slot polarity)
            (Primrec.snd.comp Primrec.snd))
      exact Computability.cell_add_primrec.comp origin localPosition
    have clauseCase : Primrec₂ fun
        (combined : Query × Sum FixedData ClauseData)
        (clause : ClauseData) =>
        Cell.add (clauseOrigin combined.1.1 clause.1)
          (clauseTriplePositionTable clause.2) := by
      change Primrec fun data :
          (Query × Sum FixedData ClauseData) × ClauseData =>
        Cell.add (clauseOrigin data.1.1.1 data.2.1)
          (clauseTriplePositionTable data.2.2)
      have origin : Primrec fun data :
          (Query × Sum FixedData ClauseData) × ClauseData =>
          clauseOrigin data.1.1.1 data.2.1 :=
        clauseOriginPrimrec.comp
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
      have localPosition : Primrec fun data :
          (Query × Sum FixedData ClauseData) × ClauseData =>
          clauseTriplePositionTable data.2.2 :=
        clauseTriplePositionTable_primrec.comp
          (Primrec.snd.comp Primrec.snd)
      exact Computability.cell_add_primrec.comp origin localPosition
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded ordinaryCase restCase).of_eq
    fun input => by cases input.2 <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
