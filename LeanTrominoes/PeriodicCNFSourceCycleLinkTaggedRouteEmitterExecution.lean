/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterParseToScanExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanToHaltExecution

/-! # Complete execution of tagged source cycle-link route emission -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def totalTime (input : SourceCycleLinkTaggedRouteEmitter.Input) : Nat :=
  scanToHaltTime input +
    parseTime input.clauseCount input.tags
      (UnaryFieldEncoderMachine.unaryFields input.targets)

noncomputable def execution
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    EvalsToInTime machine.step
      (scanHeaderCfg initialTag
        ⟨SourceCycleLinkTaggedRouteEmitter.encode input,
          [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg (SourceCycleLinkTaggedRouteEmitter.emit input)))
      (totalTime input) := by
  have parseRun := parsing_evalsInTime input.clauseCount input.tags
    (UnaryFieldEncoderMachine.unaryFields input.targets)
  have parseRun' : EvalsToInTime machine.step
      (scanHeaderCfg initialTag
        ⟨SourceCycleLinkTaggedRouteEmitter.encode input,
          [], [], [], [], [], [], [], [], [], []⟩)
      (some (scanLinksCfg initialTag
        (scanTapeData input 0 input.tags input.targets [] [])))
      (parseTime input.clauseCount input.tags
        (UnaryFieldEncoderMachine.unaryFields input.targets)) := by
    simpa [SourceCycleLinkTaggedRouteEmitter.encode,
      SeparatedProductEncoding.encode,
      UnaryFieldEncoderMachine.unaryField,
      scanTapeData, SourceCycleLinkTaggedRouteEmitter.Input.literalCount,
      List.map_append, Function.comp_def] using parseRun
  have scanRun := scanToHalt_evalsInTime input
  have whole := EvalsToInTime.trans machine.step
    (parseTime input.clauseCount input.tags
      (UnaryFieldEncoderMachine.unaryFields input.targets))
    (scanToHaltTime input) _ _ _ parseRun' scanRun
  simpa only [totalTime] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
