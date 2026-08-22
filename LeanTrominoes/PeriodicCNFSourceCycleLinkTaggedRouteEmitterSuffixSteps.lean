/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterPushTokens

/-! # Tag-dependent suffix steps for source cycle-link records -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_finishSourceTarget (tag : Tag) (data : TapeData) :
    machine.step (finishSourceTargetCfg tag data) =
      some (beginTargetRecordCfg tag
        { data with
          outputReverse :=
            (sourceSuffix tag).reverse ++
              .atomEnd :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, finishSourceTargetCfg,
    beginTargetRecordCfg, cursorCfg, cfg, program, TM2.stepAux]
  rw [update_tapes_outputReverse]
  rw [stepAux_pushTokens]
  simp only [TM2.stepAux, cursorTag, clear]
  rfl

theorem step_finishTargetRecord (tag : Tag) (data : TapeData) :
    machine.step (finishTargetRecordCfg tag data) =
      some (incrementLinkCfg tag
        { data with
          outputReverse :=
            (targetSuffix tag).reverse ++
              .atomEnd :: data.outputReverse }) := by
  simp only [FinTM2.step, TM2.step, machine, finishTargetRecordCfg,
    incrementLinkCfg, cursorCfg, cfg, program, TM2.stepAux]
  rw [update_tapes_outputReverse]
  rw [stepAux_pushTokens]
  simp only [TM2.stepAux, cursorTag, clear]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
