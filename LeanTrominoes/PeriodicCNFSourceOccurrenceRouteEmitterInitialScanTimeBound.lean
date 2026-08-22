/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterInputSizeBounds
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanFinalBudget
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanOutputBound
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanTimeBound
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterScanToHaltExecution

/-! # Initial occurrence-scan and finalization bounds -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine

theorem initial_scanTime_le (input : SourceOccurrenceRouteEmitter.Input) :
    scanTime (initialBase input.occurrences)
        (initialScanState input.targets) input.occurrences ≤
      64 * (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
  let inputLength := (SourceOccurrenceRouteEmitter.encode input).length
  let size := scanSize (initialBase input.occurrences)
    (initialScanState input.targets) input.occurrences
  have timeLe := scanTime_le (initialBase input.occurrences)
    (initialScanState input.targets) input.occurrences
  have occurrenceLe := occurrences_length_add_one_le_encode_length input
  have sizeLe := initial_scanSize_le input
  have oneLe := one_le_encode_length input
  have factorLe : 21 * size + 1 ≤ 64 * inputLength := by
    dsimp only [size, inputLength]
    omega
  have productLe := Nat.mul_le_mul occurrenceLe factorLe
  calc
    scanTime (initialBase input.occurrences)
        (initialScanState input.targets) input.occurrences ≤
      (input.occurrences.length + 1) * (21 * size + 1) := timeLe
    _ ≤ inputLength * (64 * inputLength) := productLe
    _ = 64 * inputLength ^ 2 := by ring

theorem initial_emitted_length_le
    (input : SourceOccurrenceRouteEmitter.Input) :
    (scan (initialBase input.occurrences).clauseCount.length
      (initialBase input.occurrences).literalCount.length
      (initialScanState input.targets) input.occurrences).emitted.length ≤
        45 * (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
  let inputLength := (SourceOccurrenceRouteEmitter.encode input).length
  let size := scanSize (initialBase input.occurrences)
    (initialScanState input.targets) input.occurrences
  have outputLe := scan_emitted_length_le (initialBase input.occurrences)
    (initialScanState input.targets) input.occurrences
  have occurrenceLe := occurrences_length_le_encode_length input
  have sizeLe := initial_scanSize_le input
  have factorLe : 15 * size ≤ 45 * inputLength := by
    dsimp only [size, inputLength]
    omega
  have productLe := Nat.mul_le_mul occurrenceLe factorLe
  calc
    (scan (initialBase input.occurrences).clauseCount.length
        (initialBase input.occurrences).literalCount.length
        (initialScanState input.targets) input.occurrences).emitted.length ≤
      (initialScanState input.targets).emitted.length +
        input.occurrences.length * (15 * size) := outputLe
    _ = input.occurrences.length * (15 * size) := by
      simp [initialScanState]
    _ ≤ inputLength * (45 * inputLength) := productLe
    _ = 45 * inputLength ^ 2 := by ring

theorem initial_final_scanSize_le
    (input : SourceOccurrenceRouteEmitter.Input) :
    scanSize (initialBase input.occurrences)
        (scan (initialBase input.occurrences).clauseCount.length
          (initialBase input.occurrences).literalCount.length
          (initialScanState input.targets) input.occurrences) [] ≤
      3 * (SourceOccurrenceRouteEmitter.encode input).length := by
  exact (scanSize_final_le (initialBase input.occurrences)
    (initialScanState input.targets) input.occurrences).trans
      (initial_scanSize_le input)

theorem initial_cleanupTime_le
    (input : SourceOccurrenceRouteEmitter.Input) :
    cleanupTime (scanCleanupData (initialBase input.occurrences)
      (initialScanState input.targets) input.occurrences) ≤
        13 * (SourceOccurrenceRouteEmitter.encode input).length := by
  let base := initialBase input.occurrences
  let state := initialScanState input.targets
  let final := scan base.clauseCount.length base.literalCount.length
    state input.occurrences
  have finalLe := initial_final_scanSize_le input
  have oneLe := one_le_encode_length input
  have cleanupEq : cleanupTime (scanCleanupData base state input.occurrences) =
      scanSize base final [] + 10 := by
    simp [cleanupTime, scanCleanupData, scanData, scanSize, base, final,
      initialBase]
    omega
  rw [cleanupEq]
  dsimp only [base, state, final] at finalLe ⊢
  omega

theorem initial_reverseTime_le
    (input : SourceOccurrenceRouteEmitter.Input) :
    let final := scan (initialBase input.occurrences).clauseCount.length
      (initialBase input.occurrences).literalCount.length
      (initialScanState input.targets) input.occurrences
    reverseTime final.emitted.reverse ≤
      91 * (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
  dsimp only
  have outputLe := initial_emitted_length_le input
  have oneLe := one_le_encode_length input
  have oneSquare : 1 ≤
      (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  rw [reverseTime_eq, List.length_reverse]
  omega

theorem initial_scanToHaltTime_le
    (input : SourceOccurrenceRouteEmitter.Input) :
    scanToHaltTime (initialBase input.occurrences)
        (initialScanState input.targets) input.occurrences ≤
      168 * (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
  have scanLe := initial_scanTime_le input
  have reverseLe := initial_reverseTime_le input
  have cleanupLe := initial_cleanupTime_le input
  have oneLe := one_le_encode_length input
  have linearLeSquare : (SourceOccurrenceRouteEmitter.encode input).length ≤
      (SourceOccurrenceRouteEmitter.encode input).length ^ 2 := by
    nlinarith
  simp only [scanToHaltTime]
  omega

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteEmitterMachine
