/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineCanonicalExecution
import LeanTrominoes.GadgetSparseRouteRecordMachineOutputBound

/-! # Quadratic bound for valid canonical route requests -/

namespace LeanTrominoes

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.RouteRasterRequest

theorem normalizedRequestBlock_length (request : Request) :
    (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
      request).length =
      request.metadata.period + request.metadata.cursorHorizontal +
        request.metadata.cursorVertical +
        (requestDirections request).length + 5 := by
  rw [GadgetSparseRouteRecordTokens.normalizedRequestBlock_eq]
  simp only [List.length_append, List.length_replicate,
    List.length_cons, List.length_map, List.length_nil,
    requestDirections]
  omega

@[simp] theorem complementLocation_verticalMass (metadata : Metadata) :
    verticalMass metadata.complementLocation = metadata.cursorVertical := by
  simp [verticalMass, Metadata.complementLocation]

/-- Terminal cleanup is linear in the initial cursor and direction word. -/
theorem canonicalCleanupTime_le (request : Request) :
    cleanupTime (canonicalAfterReverseData request) ≤
      request.metadata.complementLocation.period +
        verticalMass request.metadata.complementLocation +
        (requestDirections request).length + 6 := by
  let initial := request.metadata.complementLocation
  let final := advanceDirections initial (requestDirections request)
  have periodEq : final.period = initial.period := by
    simp [final, initial]
  have massLe : verticalMass final ≤
      verticalMass initial + (requestDirections request).length := by
    simpa [final, initial] using
      advanceDirections_verticalMass_le initial (requestDirections request)
  have counterEq : final.horizontal + final.horizontalComplement + 1 =
      final.period := by
    rfl
  dsimp only [final, initial] at periodEq massLe counterEq
  unfold cleanupTime canonicalAfterReverseData canonicalAfterRouteData
    locationData
  simp only [List.length_nil, List.length_replicate, zero_add,
    add_zero]
  rw [Nat.add_assoc
    ((advanceDirections request.metadata.complementLocation
      (requestDirections request)).horizontal +
      (advanceDirections request.metadata.complementLocation
        (requestDirections request)).horizontalComplement)]
  rw [signedPositive_add_signedNegative]
  omega

/-- The exact canonical execution fits a fixed quadratic in the encoded
normalized-block length. -/
theorem canonicalTotalTime_le_square (request : Request)
    (valid : request.metadata.CursorValid) :
    canonicalTotalTime request ≤
      16 *
        ((GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
          request).length + 1) ^ 2 := by
  let period := request.metadata.period
  let horizontal := request.metadata.cursorHorizontal
  let vertical := request.metadata.cursorVertical
  let directions := requestDirections request
  let length :=
    (GadgetSparseRouteRasterNormalizedTokens.normalizedRequestBlock
      request).length
  have lengthEq : length =
      period + horizontal + vertical + directions.length + 5 := by
    simpa [length, period, horizontal, vertical, directions] using
      normalizedRequestBlock_length request
  have periodEq : request.metadata.complementLocation.period = period := by
    simpa [period] using request.metadata.complementLocation_period valid
  have massEq :
      verticalMass request.metadata.complementLocation = vertical := by
    simp [vertical]
  have directionLe : directions.length + 1 ≤ length := by
    omega
  have routeScaleLe :
      request.metadata.complementLocation.period +
          verticalMass request.metadata.complementLocation +
          directions.length + 1 ≤ length := by
    rw [periodEq, massEq]
    omega
  have metadataBound : metadataTime request ≤ 2 * length := by
    unfold metadataTime
    change period + 1 + 2 * horizontal + 2 + (vertical + 1) + 1 ≤
      2 * length
    omega
  have routeRaw := routeTime_le request.metadata.complementLocation directions
  have routeBound :
      routeTime request.metadata.complementLocation directions ≤
        4 * length ^ 2 := by
    calc
      routeTime request.metadata.complementLocation directions ≤
          4 * (directions.length + 1) *
            (request.metadata.complementLocation.period +
              verticalMass request.metadata.complementLocation +
              directions.length + 1) := routeRaw
      _ ≤ 4 * length * length :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 directionLe) routeScaleLe
      _ = 4 * length ^ 2 := by ring
  have outputRaw := complementRecordBlock_length_le request
  have outputScaleLe :
      request.metadata.complementLocation.period +
          verticalMass request.metadata.complementLocation +
          directions.length + 2 ≤ length := by
    rw [periodEq, massEq]
    omega
  have directionLengthLe : directions.length ≤ length := by omega
  have outputBound :
      (complementRecordBlock request).length ≤ length ^ 2 := by
    change (complementRecordBlock request).length ≤ _ at outputRaw
    simpa [directions, pow_two] using outputRaw.trans
      (Nat.mul_le_mul directionLengthLe outputScaleLe)
  have cleanupRaw := canonicalCleanupTime_le request
  have cleanupBound :
      cleanupTime (canonicalAfterReverseData request) ≤ length + 1 := by
    calc
      cleanupTime (canonicalAfterReverseData request) ≤
          request.metadata.complementLocation.period +
            verticalMass request.metadata.complementLocation +
            (requestDirections request).length + 6 := cleanupRaw
      _ = period + vertical + directions.length + 6 := by
        rw [periodEq, massEq]
      _ ≤ length + 1 := by omega
  unfold canonicalTotalTime canonicalRouteTime canonicalFinishTime
  nlinarith [Nat.zero_le length]

end GadgetSparseRouteRecordMachine
end LeanTrominoes
