/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterExecution
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterOutputLengthBound
import LeanTrominoes.PeriodicCNFSourceCycleLinkTaggedRouteEmitterScanTimeBound

/-! # Quadratic total-time bound for tagged cycle-link route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine

theorem cleanupTime_reversedData_eq
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    cleanupTime (reversedData input) =
      input.clauseCount + 2 * input.literalCount + 10 := by
  simp [cleanupTime, reversedData, scanTapeData, counterCleanupTime,
    streamCleanupTime, streamCleanupData, afterCleanupTargetReverse,
    afterCleanupTags, afterCleanupTagReverse, afterCleanupInput,
    SourceCycleLinkTaggedRouteEmitter.Input.literalCount]
  omega

theorem cleanupTime_reversedData_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    cleanupTime (reversedData input) ≤
      4 * (SourceCycleLinkTaggedRouteEmitter.encode input).length := by
  rw [cleanupTime_reversedData_eq, encode_length]
  omega

theorem reverseTime_emit_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    reverseTime (SourceCycleLinkTaggedRouteEmitter.emit input).reverse ≤
      61 * (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
  have outputLe := emit_length_le input
  have oneLe := one_le_encode_length input
  have oneSquare :
      1 ≤ (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  rw [reverseTime_eq, List.length_reverse]
  omega

theorem scanToHaltTime_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    scanToHaltTime input ≤
      122 * (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
  have scanLe := initial_scanTime_le input
  have reverseLe := reverseTime_emit_le input
  have cleanupLe := cleanupTime_reversedData_le input
  have oneLe := one_le_encode_length input
  have linearLeSquare :
      (SourceCycleLinkTaggedRouteEmitter.encode input).length ≤
        (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  simp only [scanToHaltTime]
  omega

theorem totalTime_le
    (input : SourceCycleLinkTaggedRouteEmitter.Input) :
    totalTime input ≤
      126 * (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
  have scanLe := scanToHaltTime_le input
  have parseLe := parseTime_le_four_encode_length input
  have oneLe := one_le_encode_length input
  have linearLeSquare :
      (SourceCycleLinkTaggedRouteEmitter.encode input).length ≤
        (SourceCycleLinkTaggedRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  simp only [totalTime]
  omega

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTaggedRouteEmitterMachine
