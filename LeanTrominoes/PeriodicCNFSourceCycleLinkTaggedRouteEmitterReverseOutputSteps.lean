/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # Output-reversal steps for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_reverseOutput_nil (tag : Tag) (data : TapeData)
    (outputReverseEq : data.outputReverse = []) :
    machine.step (reverseOutputCfg tag data) =
      some (cleanupCfg .input tag { data with outputReverse := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    cleanupCfg, cursorCfg, cfg, program, TM2.stepAux, tapes,
    List.head?_nil, List.tail_nil, outputIsNone, cursorTag,
    clear, update_tapes_outputReverse]
  rfl

theorem step_reverseOutput_cons (tag : Tag) (data : TapeData)
    (token : OutputToken) (remaining : List OutputToken)
    (outputReverseEq : data.outputReverse = token :: remaining) :
    machine.step (reverseOutputCfg tag data) =
      some (pushOutputCfg tag token
        { data with outputReverse := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change outputReverse = token :: remaining at outputReverseEq
  subst outputReverse
  simp only [FinTM2.step, TM2.step, machine, reverseOutputCfg,
    pushOutputCfg, outputCfg, cursorCfg, cfg, program, TM2.stepAux,
    tapes, List.head?_cons, List.tail_cons, outputIsNone,
    cursorTag, update_tapes_outputReverse]
  rfl

theorem step_pushOutput (tag : Tag) (data : TapeData)
    (token : OutputToken) :
    machine.step (pushOutputCfg tag token data) =
      some (reverseOutputCfg tag
        { data with output := token :: data.output }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, pushOutputCfg,
    reverseOutputCfg, outputCfg, cursorCfg, cfg, program, TM2.stepAux,
    outputFromState, cursorTag, clear, update_tapes_output]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
