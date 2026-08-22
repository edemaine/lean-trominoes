/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterCleanupExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterReverseOutputExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanExecution

/-! # Tagged cycle-link scanning through machine halt -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

def scannedData (input : SourceCycleLinkTaggedRouteEmitter.Input) : TapeData :=
  scanTapeData input input.tags.length [] []
    (SourceCycleLinkTaggedRouteEmitter.emit input).reverse []

def reversedData (input : SourceCycleLinkTaggedRouteEmitter.Input) : TapeData :=
  scanTapeData input input.tags.length [] [] []
    (SourceCycleLinkTaggedRouteEmitter.emit input)

def scanToHaltTime
    (input : SourceCycleLinkTaggedRouteEmitter.Input) : Nat :=
  cleanupTime (reversedData input) +
    (reverseTime (SourceCycleLinkTaggedRouteEmitter.emit input).reverse +
      scanTime input 0 input.tags input.targets [] [])

noncomputable def scanToHalt_evalsInTime
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    EvalsToInTime machine.step
      (scanLinksCfg initialTag
        (scanTapeData input 0 input.tags input.targets [] []))
      (some (haltCfg (SourceCycleLinkTaggedRouteEmitter.emit input)))
      (scanToHaltTime input) := by
  have scanRun := scanLinks_evalsInTime input initialTag 0
    input.tags input.targets [] [] input.valid
  have scanRun' : EvalsToInTime machine.step
      (scanLinksCfg initialTag
        (scanTapeData input 0 input.tags input.targets [] []))
      (some (reverseOutputCfg (finalTag initialTag input.tags)
        (scannedData input)))
      (scanTime input 0 input.tags input.targets [] []) := by
    simpa [scannedData, SourceCycleLinkTaggedRouteEmitter.emit] using scanRun
  have reverseRun := reverseOutput_evalsInTime
    (finalTag initialTag input.tags) (scannedData input)
    (SourceCycleLinkTaggedRouteEmitter.emit input).reverse rfl
  have reverseRun' : EvalsToInTime machine.step
      (reverseOutputCfg (finalTag initialTag input.tags)
        (scannedData input))
      (some (cleanupCfg .input (finalTag initialTag input.tags)
        (reversedData input)))
      (reverseTime (SourceCycleLinkTaggedRouteEmitter.emit input).reverse) := by
    simpa [scannedData, reversedData, scanTapeData] using reverseRun
  have cleanupRun := cleanup_evalsInTime
    (finalTag initialTag input.tags) (reversedData input)
  have throughCleanup := EvalsToInTime.trans machine.step
    (reverseTime (SourceCycleLinkTaggedRouteEmitter.emit input).reverse)
    (cleanupTime (reversedData input)) _ _ _ reverseRun' cleanupRun
  have whole := EvalsToInTime.trans machine.step
    (scanTime input 0 input.tags input.targets [] [])
    (cleanupTime (reversedData input) +
      reverseTime (SourceCycleLinkTaggedRouteEmitter.emit input).reverse)
    _ _ _ scanRun' throughCleanup
  simpa [scanToHaltTime, reversedData, scanTapeData,
    Nat.add_assoc] using whole

end PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
end LeanTrominoes
