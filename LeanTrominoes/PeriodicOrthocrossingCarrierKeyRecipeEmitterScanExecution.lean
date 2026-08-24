/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScanSteps

/-! # Complete input scan of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

theorem replicate_unit_succ_right (count : Nat) :
    List.replicate (count + 1) () =
      List.replicate count () ++ [()] := by
  rw [List.replicate_add]
  rfl

def scan_evalsInTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (data : TapeData)
    (inputEq : data.input = input) (payloadEq : state.payload = none) :
    EvalsToInTime (TM2.step (program recipes))
      (scanCfg state data)
      (some (beginEmissionCfg recipes (scanState state input)
        { data with
          input := []
          firstRoute := routeUnits input .first ++ data.firstRoute
          secondRoute := routeUnits input .second ++ data.secondRoute }))
      (input.length + 1) := by
  induction input generalizing state data with
  | nil =>
      have step := oneStep
        (step_scan_nil recipes state data inputEq payloadEq)
      convert step using 1 <;>
        simp [scanState, routeUnits, CarrierKeyRecipeEmitter.routeCount]
  | cons token input induction =>
      cases token with
      | routeUnit side =>
          cases side with
          | first =>
              let nextData : TapeData :=
                { data with
                  input := input
                  firstRoute := () :: data.firstRoute }
              have first := oneStep
                (step_scan_firstRoute recipes state data input inputEq
                  payloadEq)
              have rest := induction state nextData rfl payloadEq
              have composed := EvalsToInTime.trans
                (TM2.step (program recipes)) 1 (input.length + 1)
                (scanCfg state data) (scanCfg state nextData)
                (some (beginEmissionCfg recipes
                  (scanState state input)
                  { nextData with
                    input := []
                    firstRoute :=
                      routeUnits input .first ++ nextData.firstRoute
                    secondRoute :=
                      routeUnits input .second ++ nextData.secondRoute }))
                first rest
              convert composed using 1
              · simp [scanState, scanToken, nextData, routeUnits,
                  CarrierKeyRecipeEmitter.routeCount,
                  replicate_unit_succ_right, List.append_assoc,
                  clearPayload_eq_self state payloadEq]
              · simp
          | second =>
              let nextData : TapeData :=
                { data with
                  input := input
                  secondRoute := () :: data.secondRoute }
              have first := oneStep
                (step_scan_secondRoute recipes state data input inputEq
                  payloadEq)
              have rest := induction state nextData rfl payloadEq
              have composed := EvalsToInTime.trans
                (TM2.step (program recipes)) 1 (input.length + 1)
                (scanCfg state data) (scanCfg state nextData)
                (some (beginEmissionCfg recipes
                  (scanState state input)
                  { nextData with
                    input := []
                    firstRoute :=
                      routeUnits input .first ++ nextData.firstRoute
                    secondRoute :=
                      routeUnits input .second ++ nextData.secondRoute }))
                first rest
              convert composed using 1
              · simp [scanState, scanToken, nextData, routeUnits,
                  CarrierKeyRecipeEmitter.routeCount,
                  replicate_unit_succ_right, List.append_assoc,
                  clearPayload_eq_self state payloadEq]
              · simp
      | activation active =>
          let nextState : State recipes.length :=
            { actives := FixedLengthWordEvaluator.shiftAppend
                state.actives active
              payload := none }
          let nextData : TapeData := { data with input := input }
          have first := oneStep
            (step_scan_activation recipes state data active input inputEq
              payloadEq)
          have rest := induction nextState nextData rfl rfl
          have composed := EvalsToInTime.trans
            (TM2.step (program recipes)) 1 (input.length + 1)
            (scanCfg state data) (scanCfg nextState nextData)
            (some (beginEmissionCfg recipes
              (scanState nextState input)
              { nextData with
                input := []
                firstRoute :=
                  routeUnits input .first ++ nextData.firstRoute
                secondRoute :=
                  routeUnits input .second ++ nextData.secondRoute }))
            first rest
          convert composed using 1
          · simp [scanState, scanToken, nextState, nextData, routeUnits,
              CarrierKeyRecipeEmitter.routeCount]
          · simp

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
