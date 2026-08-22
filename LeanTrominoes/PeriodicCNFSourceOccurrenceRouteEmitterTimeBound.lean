/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecution
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInitialScanTimeBound

/-! # Quadratic total-time bound for source-occurrence route emission -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem totalTime_le (input : SourceOccurrenceRouteEmitter.Input) :
    totalTime input ≤
      172 * (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
  have scanLe := initial_scanToHaltTime_le input
  have parseEq := parseTime_eq_four_encode_length input
  have oneLe := one_le_encode_length input
  have linearLeSquare : (SourceOccurrenceRouteEmitter.encode input).length ≤
      (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  simp only [totalTime]
  rw [parseEq]
  omega

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
