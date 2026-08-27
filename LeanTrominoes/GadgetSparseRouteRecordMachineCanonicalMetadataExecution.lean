/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineFieldExecution

/-! # Canonical metadata execution for normalized route requests -/

namespace LeanTrominoes

open Computability StateTransition Turing

noncomputable section

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.RouteRasterRequest

abbrev Request := PeriodicCNFStripReduction.RouteRasterRequest.Request

def requestDirections (request : Request) : List AxisDirection :=
  (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
    request.normalization).directions

def metadataTime (request : Request) : Nat :=
  request.metadata.period + 1 +
    2 * request.metadata.cursorHorizontal + 2 +
    (request.metadata.cursorVertical + 1) + 1

theorem replicate_split_reserved {period horizontal : Nat}
    (valid : horizontal < period) :
    List.replicate period () =
      List.replicate horizontal () ++
        () :: List.replicate (period - horizontal - 1) () := by
  rw [← List.replicate_succ]
  rw [← List.replicate_add]
  congr 1
  omega

/-- Parsing the canonical unary metadata reaches exactly the certified
complement location and leaves the normalized direction suffix untouched. -/
def canonicalMetadata_evalsInTime (request : Request)
    (valid : request.metadata.CursorValid) :
    EvalsToInTime (TM2.step program)
      (scanPeriodCfg (initialData
        (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request)))
      (some (cfg (.scanIncoming request.metadata.color)
        (inputState (.color request.metadata.color))
        (locationData
          (directionInput (requestDirections request) [.routeEnd])
          request.metadata.complementLocation [] [])))
      (metadataTime request) := by
  let period := request.metadata.period
  let horizontal := request.metadata.cursorHorizontal
  let vertical := request.metadata.cursorVertical
  let directions := requestDirections request
  let directionTokens := directionInput directions [.routeEnd]
  let colorInput : List InputToken :=
    .color request.metadata.color :: directionTokens
  let verticalInput : List InputToken :=
    List.replicate vertical .unit ++ .verticalEnd :: colorInput
  let horizontalEndInput : List InputToken :=
    .horizontalEnd :: verticalInput
  let horizontalInput : List InputToken :=
    List.replicate horizontal .unit ++ horizontalEndInput
  let initial := initialData
    (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock request)
  let afterPeriod : TapeData :=
    { input := horizontalInput
      horizontal := []
      horizontalComplement := List.replicate period ()
      verticalPositive := []
      verticalNegative := []
      scratch := []
      outputReverse := []
      output := [] }
  let reserved := List.replicate (period - horizontal - 1) ()
  let afterHorizontal : TapeData :=
    { afterPeriod with
      input := horizontalEndInput
      horizontal := List.replicate horizontal ()
      horizontalComplement := () :: reserved }
  let afterFinish : TapeData :=
    { afterHorizontal with
      input := verticalInput
      horizontalComplement := reserved }
  let afterVertical : TapeData :=
    { afterFinish with
      input := colorInput
      verticalPositive :=
        (List.replicate vertical ()).reverse ++
          afterFinish.verticalPositive }
  let afterColor := locationData directionTokens
    request.metadata.complementLocation [] []
  let periodWord := List.replicate period ()
  have periodRun := scanPeriodUnits_evalsInTime periodWord horizontalInput
    initial (by
      change GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request =
        List.replicate periodWord.length .unit ++
          .periodEnd :: horizontalInput
      rw [GadgetSparseRouteRecordTokens.normalizedRequestBlock_eq]
      simp [periodWord, period, horizontalInput, horizontalEndInput,
        verticalInput, colorInput, directionTokens, directions,
        requestDirections, directionInput, horizontal, vertical])
  have periodRun' : EvalsToInTime (TM2.step program)
      (scanPeriodCfg initial) (some (scanHorizontalCfg afterPeriod))
      (period + 1) := by
    simpa [periodWord, initial, afterPeriod, initialData] using periodRun
  have valid' : horizontal < period := by
    simpa [horizontal, period, Metadata.CursorValid] using valid
  let horizontalWord := List.replicate horizontal ()
  have horizontalRun := scanHorizontalUnits_evalsInTime horizontalWord
    (() :: reserved) horizontalEndInput afterPeriod
    (by simp [afterPeriod, horizontalInput, horizontalWord])
    (by
      simp only [afterPeriod]
      change List.replicate period () =
        List.replicate horizontal () ++ () :: reserved
      simpa [reserved] using replicate_split_reserved valid')
  have horizontalRun' : EvalsToInTime (TM2.step program)
      (scanHorizontalCfg afterPeriod)
      (some (scanHorizontalCfg afterHorizontal)) (2 * horizontal) := by
    simpa [horizontalWord, afterHorizontal, afterPeriod] using horizontalRun
  have finishRun := finishHorizontal_evalsInTime reserved verticalInput
    afterHorizontal (by simp [afterHorizontal, horizontalEndInput])
    (by simp [afterHorizontal])
  have finishRun' : EvalsToInTime (TM2.step program)
      (scanHorizontalCfg afterHorizontal)
      (some (scanVerticalCfg afterFinish)) 2 := by
    simpa [afterFinish] using finishRun
  let verticalWord := List.replicate vertical ()
  have verticalRun := scanVerticalUnits_evalsInTime verticalWord colorInput
    afterFinish (by
      simp [afterFinish, verticalInput, verticalWord])
  have verticalRun' : EvalsToInTime (TM2.step program)
      (scanVerticalCfg afterFinish)
      (some (scanColorCfg afterVertical)) (vertical + 1) := by
    simpa [verticalWord, afterVertical] using verticalRun
  have colorRun := oneStep (step_scanColor_color none afterVertical
    request.metadata.color directionTokens (by
      simp [afterVertical, colorInput]))
  have colorRun' : EvalsToInTime (TM2.step program)
      (scanColorCfg afterVertical)
      (some (cfg (.scanIncoming request.metadata.color)
        (inputState (.color request.metadata.color)) afterColor)) 1 := by
    simpa [scanColorCfg, labelCfg, afterColor, afterVertical,
      directionTokens, locationData, Metadata.complementLocation,
      signedPositive, signedNegative,
      horizontal, vertical, period, reserved, afterFinish,
      afterHorizontal, afterPeriod] using colorRun
  have throughHorizontal := EvalsToInTime.trans (TM2.step program)
    (period + 1) (2 * horizontal)
    (scanPeriodCfg initial) (scanHorizontalCfg afterPeriod)
    (some (scanHorizontalCfg afterHorizontal)) periodRun' horizontalRun'
  have throughFinish := EvalsToInTime.trans (TM2.step program)
    (2 * horizontal + (period + 1)) 2
    (scanPeriodCfg initial) (scanHorizontalCfg afterHorizontal)
    (some (scanVerticalCfg afterFinish)) throughHorizontal finishRun'
  have throughVertical := EvalsToInTime.trans (TM2.step program)
    (2 + (2 * horizontal + (period + 1))) (vertical + 1)
    (scanPeriodCfg initial) (scanVerticalCfg afterFinish)
    (some (scanColorCfg afterVertical)) throughFinish verticalRun'
  have whole := EvalsToInTime.trans (TM2.step program)
    ((vertical + 1) + (2 + (2 * horizontal + (period + 1)))) 1
    (scanPeriodCfg initial) (scanColorCfg afterVertical)
    (some (cfg (.scanIncoming request.metadata.color)
      (inputState (.color request.metadata.color)) afterColor))
    throughVertical colorRun'
  convert whole using 1
  simp [metadataTime, period, horizontal, vertical]
  omega

end GadgetSparseRouteRecordMachine
end
end LeanTrominoes
