/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # Unary target-field steps for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_scanTarget_nil (tag : Tag) (data : TapeData)
    (targetsEq : data.targets = []) :
    machine.step (scanTargetCfg tag data) =
      some (finishSourceTargetCfg tag { data with targets := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change targets = [] at targetsEq
  subst targets
  simp only [FinTM2.step, TM2.step, machine, scanTargetCfg,
    finishSourceTargetCfg, cursorCfg, cfg, program, TM2.stepAux, tapes,
    List.head?_nil, List.tail_nil, unaryIsNone, cursorTag, clear,
    update_tapes_targets]
  rfl

theorem step_scanTarget_unit (tag : Tag) (data : TapeData)
    (remaining : List UnarySymbol)
    (targetsEq : data.targets = .unit :: remaining) :
    machine.step (scanTargetCfg tag data) =
      some (scanTargetCfg tag
        { data with
          targets := remaining
          outputReverse := .atomUnit :: data.outputReverse }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change targets = .unit :: remaining at targetsEq
  subst targets
  simp only [FinTM2.step, TM2.step, machine, scanTargetCfg,
    cursorCfg, cfg, program, TM2.stepAux, tapes, List.head?_cons,
    List.tail_cons, unaryIsNone, unaryIsUnit, cursorTag, clear,
    update_tapes_targets, update_tapes_outputReverse]
  rfl

theorem step_scanTarget_delimiter (tag : Tag) (data : TapeData)
    (remaining : List UnarySymbol)
    (targetsEq : data.targets = .delimiter :: remaining) :
    machine.step (scanTargetCfg tag data) =
      some (finishSourceTargetCfg tag
        { data with targets := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change targets = .delimiter :: remaining at targetsEq
  subst targets
  simp only [FinTM2.step, TM2.step, machine, scanTargetCfg,
    finishSourceTargetCfg, cursorCfg, cfg, program, TM2.stepAux, tapes,
    List.head?_cons, List.tail_cons, unaryIsNone, unaryIsUnit,
    cursorTag, clear, update_tapes_targets]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
