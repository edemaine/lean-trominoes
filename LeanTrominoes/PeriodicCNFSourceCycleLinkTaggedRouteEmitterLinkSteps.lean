/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCounterTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterInputTapeUpdates
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputTapeUpdates

/-! # Link-boundary steps for tagged source cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

open Turing

theorem step_scanLinks_nil (tag : Tag) (data : TapeData)
    (tagsEq : data.tags = []) :
    machine.step (scanLinksCfg tag data) =
      some (reverseOutputCfg tag { data with tags := [] }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change tags = [] at tagsEq
  subst tags
  simp only [FinTM2.step, TM2.step, machine, scanLinksCfg,
    reverseOutputCfg, cursorCfg, cfg, program, TM2.stepAux,
    tagIsNone, cursorTag, clear, update_tapes_tags]
  rfl

theorem step_scanLinks_cons (cursor current : Tag) (data : TapeData)
    (remaining : List Tag)
    (tagsEq : data.tags = current :: remaining) :
    machine.step (scanLinksCfg cursor data) =
      some (beginSourceRecordCfg current
        { data with tags := remaining }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  change tags = _ at tagsEq
  subst tags
  cases current <;>
    simp only [FinTM2.step, TM2.step, machine, scanLinksCfg,
      beginSourceRecordCfg, cursorCfg, cfg, program, TM2.stepAux,
      tagIsNone, tagFromState, cursorTag, clear, update_tapes_tags] <;>
    rfl

theorem step_beginSourceRecord (tag : Tag) (data : TapeData) :
    machine.step (beginSourceRecordCfg tag data) =
      some (copyCounterCfg .sourceVertexClause tag
        { data with
          outputReverse := .clauseMarker :: data.outputReverse }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, beginSourceRecordCfg,
    copyCounterCfg, cursorCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

theorem step_beginTargetRecord (tag : Tag) (data : TapeData) :
    machine.step (beginTargetRecordCfg tag data) =
      some (copyCounterCfg .targetVertexClause tag
        { data with
          outputReverse := .clauseMarker :: data.outputReverse }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, beginTargetRecordCfg,
    copyCounterCfg, cursorCfg, cfg, program, TM2.stepAux,
    update_tapes_outputReverse]
  rfl

theorem step_incrementLink (tag : Tag) (data : TapeData) :
    machine.step (incrementLinkCfg tag data) =
      some (scanLinksCfg tag
        { data with linkIndex := () :: data.linkIndex }) := by
  rcases data with ⟨input, tagReverse, tags, targetReverse, targets,
    clauseCount, literalCount, linkIndex, scratch, outputReverse, output⟩
  simp only [FinTM2.step, TM2.step, machine, incrementLinkCfg,
    scanLinksCfg, cursorCfg, cfg, program, TM2.stepAux, cursorTag, clear,
    update_tapes_linkIndex]
  rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
