/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRouteScanSteps

/-! # Complete route-counter scans of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem replicate_succ_right (count : Nat) (value : α) :
    List.replicate (count + 1) value =
      List.replicate count value ++ [value] := by
  rw [List.replicate_add]
  rfl

def scanRouteFirst_evalsInTime (recipes : List Recipe)
    (index : Fin recipes.length)
    (sideEq : (recipes.get index).side = .first)
    (word : List Unit) (state : State recipes.length) (data : TapeData)
    (routeEq : data.firstRoute = word)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (scanRouteCfg index state data)
      (some (restoreRouteCfg index state
        { data with
          firstRoute := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate word.length (.bit false) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanRoute_first_nil recipes index state data sideEq routeEq
          payloadEq)
      convert step using 1 <;> simp
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData :=
        { data with
          firstRoute := word
          scratch := () :: data.scratch
          outputReverse := .bit false :: data.outputReverse }
      have first := oneStep
        (step_scanRoute_first_cons recipes index state data sideEq word
          routeEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (scanRouteCfg index state data)
        (scanRouteCfg index state nextData)
        (some (restoreRouteCfg index state
          { nextData with
            firstRoute := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate word.length (.bit false) ++
                nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc,
          replicate_succ_right]
      · simp

def scanRouteSecond_evalsInTime (recipes : List Recipe)
    (index : Fin recipes.length)
    (sideEq : (recipes.get index).side = .second)
    (word : List Unit) (state : State recipes.length) (data : TapeData)
    (routeEq : data.secondRoute = word)
    (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (scanRouteCfg index state data)
      (some (restoreRouteCfg index state
        { data with
          secondRoute := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate word.length (.bit false) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanRoute_second_nil recipes index state data sideEq routeEq
          payloadEq)
      convert step using 1 <;> simp
  | cons item word induction =>
      have itemEq : item = () := Subsingleton.elim _ _
      subst item
      let nextData : TapeData :=
        { data with
          secondRoute := word
          scratch := () :: data.scratch
          outputReverse := .bit false :: data.outputReverse }
      have first := oneStep
        (step_scanRoute_second_cons recipes index state data sideEq word
          routeEq payloadEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program recipes)) 1 (word.length + 1)
        (scanRouteCfg index state data)
        (scanRouteCfg index state nextData)
        (some (restoreRouteCfg index state
          { nextData with
            secondRoute := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate word.length (.bit false) ++
                nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc,
          replicate_succ_right]
      · simp

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
