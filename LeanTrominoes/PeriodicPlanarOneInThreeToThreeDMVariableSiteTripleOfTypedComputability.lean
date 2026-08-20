/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteTripleEncoding
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteDrawing
import LeanTrominoes.FiniteDomainComputability

/-! # Computability of typed-to-local variable triples -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

local instance variableSiteTripleInhabited : Inhabited VariableSiteTriple :=
  ⟨.ordinary .first .fixedGreen .first⟩

theorem variableSiteTripleOfTyped_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (@variableSiteTripleOfTyped Variable) := by
  let OrdinaryData :=
    ((Variable × OccurrenceSlot) × VariableOccurrenceVariant) ×
      VariableOccurrenceTriple
  let FixedData :=
    (Variable × OccurrenceSlot) × FixedRedConnectorTriple
  let ClauseData := Nat × X3CClauseSet
  have encoded : Primrec fun triple : Triple Variable =>
      tripleEquivData triple :=
    Primrec.of_equiv
  have ordinaryTable : Primrec fun data :
      (OccurrenceSlot × VariableOccurrenceVariant) ×
        VariableOccurrenceTriple =>
      VariableSiteTriple.ordinary
        (occurrenceVariableSiteSlot data.1.1) data.1.2 data.2 :=
    Computability.finiteDomain_primrec _
  have ordinaryCase : Primrec₂ fun (_triple : Triple Variable)
      (ordinary : OrdinaryData) =>
      VariableSiteTriple.ordinary
        (occurrenceVariableSiteSlot ordinary.1.1.2)
        ordinary.1.2 ordinary.2 := by
    change Primrec fun combined : Triple Variable × OrdinaryData =>
      VariableSiteTriple.ordinary
        (occurrenceVariableSiteSlot combined.2.1.1.2)
        combined.2.1.2 combined.2.2
    exact ordinaryTable.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd))
  have fixedTable : Primrec fun data :
      OccurrenceSlot × FixedRedConnectorTriple =>
      VariableSiteTriple.fixedRed
        (occurrenceVariableSiteSlot data.1) data.2 :=
    Computability.finiteDomain_primrec _
  have fixedCase : Primrec₂ fun
      (_combined : Triple Variable × Sum FixedData ClauseData)
      (fixed : FixedData) =>
      VariableSiteTriple.fixedRed
        (occurrenceVariableSiteSlot fixed.1.2) fixed.2 := by
    change Primrec fun data :
        (Triple Variable × Sum FixedData ClauseData) × FixedData =>
      VariableSiteTriple.fixedRed
        (occurrenceVariableSiteSlot data.2.1.2) data.2.2
    exact fixedTable.comp
      (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  have clauseCase : Primrec₂ fun
      (_combined : Triple Variable × Sum FixedData ClauseData)
      (_clause : ClauseData) =>
      VariableSiteTriple.ordinary .first .fixedGreen .first :=
    Primrec.const _
  have restCase : Primrec₂ fun (triple : Triple Variable)
      (rest : Sum FixedData ClauseData) =>
      match rest with
      | .inl fixed =>
          VariableSiteTriple.fixedRed
            (occurrenceVariableSiteSlot fixed.1.2) fixed.2
      | .inr _ =>
          VariableSiteTriple.ordinary .first .fixedGreen .first := by
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded ordinaryCase restCase).of_eq
    fun triple => by cases triple <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
