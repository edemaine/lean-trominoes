/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceRouteComputability
import LeanTrominoes.PeriodicCNFStripHorizontalClauseIncidenceRouteComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOrdinaryTypedIncidenceRouteInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalFixedRedTypedIncidenceRouteInputComputability
import LeanTrominoes.PeriodicCNFStripHorizontalClauseTypedIncidenceRouteInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Computability of complete typed incidence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalTypedIncidenceRouteComputed_primrec :
    Primrec horizontalTypedIncidenceRouteComputed := by
  have encoded : Primrec fun input : HorizontalTypedIncidenceRouteInput =>
      tripleEquivData input.1.2 :=
    (Primrec.of_equiv : Primrec (@tripleEquivData RoutedVariable)).comp
      (Primrec.snd.comp Primrec.fst)
  have ordinaryCase : Primrec₂ fun
      (input : HorizontalTypedIncidenceRouteInput)
      (ordinary : HorizontalOrdinaryTypedIncidenceData) =>
      horizontalVariableTypedIncidenceRouteComputed
        (horizontalOrdinaryTypedIncidenceRouteInputComputed (input, ordinary)) :=
    horizontalVariableTypedIncidenceRouteComputed_primrec.comp
      horizontalOrdinaryTypedIncidenceRouteInputComputed_primrec
  have fixedCase : Primrec₂ fun
      (combined : HorizontalTypedIncidenceRouteInput ×
        Sum HorizontalFixedRedTypedIncidenceData
          HorizontalClauseTypedIncidenceData)
      (fixed : HorizontalFixedRedTypedIncidenceData) =>
      horizontalVariableTypedIncidenceRouteComputed
        (horizontalFixedRedTypedIncidenceRouteInputComputed
          (combined.1, fixed)) :=
    horizontalVariableTypedIncidenceRouteComputed_primrec.comp
      (horizontalFixedRedTypedIncidenceRouteInputComputed_primrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have clauseCase : Primrec₂ fun
      (combined : HorizontalTypedIncidenceRouteInput ×
        Sum HorizontalFixedRedTypedIncidenceData
          HorizontalClauseTypedIncidenceData)
      (clause : HorizontalClauseTypedIncidenceData) =>
      horizontalClauseIncidenceRouteComputed
        (horizontalClauseTypedIncidenceRouteInputComputed
          (combined.1, clause)) :=
    horizontalClauseIncidenceRouteComputed_primrec.comp
      (horizontalClauseTypedIncidenceRouteInputComputed_primrec.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  have restCase : Primrec₂ fun
      (input : HorizontalTypedIncidenceRouteInput)
      (rest : Sum HorizontalFixedRedTypedIncidenceData
        HorizontalClauseTypedIncidenceData) =>
      match rest with
      | .inl fixed =>
          horizontalVariableTypedIncidenceRouteComputed
            (horizontalFixedRedTypedIncidenceRouteInputComputed
              (input, fixed))
      | .inr clause =>
          horizontalClauseIncidenceRouteComputed
            (horizontalClauseTypedIncidenceRouteInputComputed
              (input, clause)) := by
    exact (Primrec.sumCasesOn Primrec.snd fixedCase clauseCase).of_eq
      fun combined => by cases combined.2 <;> rfl
  exact (Primrec.sumCasesOn encoded ordinaryCase restCase).of_eq
    fun input => by
      rcases input with ⟨⟨source, triple⟩, color⟩
      cases triple <;> rfl

end PeriodicCNFStripReduction
end LeanTrominoes
