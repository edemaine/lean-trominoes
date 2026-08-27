/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachineRouteExecution

/-! # Size potentials for the complement-counter route machine -/

namespace LeanTrominoes

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction

/-- Total unary magnitude of the signed vertical counter. -/
def verticalMass (location : ComplementLocation) : Nat :=
  location.vertical.natAbs

theorem signedPositive_le_verticalMass (location : ComplementLocation) :
    signedPositive location.vertical ≤ verticalMass location := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases vertical <;> simp [signedPositive, verticalMass]

theorem signedPositive_add_signedNegative
    (location : ComplementLocation) :
    signedPositive location.vertical + signedNegative location.vertical =
      verticalMass location := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases vertical <;> simp [signedPositive, signedNegative, verticalMass]

theorem horizontal_le_period (location : ComplementLocation) :
    location.horizontal ≤ location.period := by
  unfold ComplementLocation.period
  omega

theorem advance_verticalMass_le_add_one
    (location : ComplementLocation) (direction : AxisDirection) :
    verticalMass (advanceComplementLocation location direction) ≤
      verticalMass location + 1 := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases direction with
  | east =>
      simp only [advanceComplementLocation]
      split <;> simp [verticalMass]
  | north =>
      change (vertical - 1).natAbs ≤ vertical.natAbs + 1
      simpa using Int.natAbs_sub_le vertical 1
  | west =>
      simp only [advanceComplementLocation]
      split <;> simp [verticalMass]
  | south =>
      change (vertical + 1).natAbs ≤ vertical.natAbs + 1
      simpa using Int.natAbs_add_le vertical 1
  | invalid =>
      simp [advanceComplementLocation, verticalMass]

@[simp] theorem advanceDirections_period
    (location : ComplementLocation) (directions : List AxisDirection) :
    (advanceDirections location directions).period = location.period := by
  induction directions generalizing location with
  | nil => rfl
  | cons direction directions induction =>
      simp only [advanceDirections]
      rw [induction, advanceComplementLocation_period]

theorem advanceDirections_verticalMass_le
    (location : ComplementLocation) (directions : List AxisDirection) :
    verticalMass (advanceDirections location directions) ≤
      verticalMass location + directions.length := by
  induction directions generalizing location with
  | nil => simp [advanceDirections]
  | cons direction directions induction =>
      simp only [advanceDirections, List.length_cons]
      calc
        verticalMass
            (advanceDirections
              (advanceComplementLocation location direction) directions) ≤
          verticalMass (advanceComplementLocation location direction) +
            directions.length := induction _
        _ ≤ (verticalMass location + 1) + directions.length :=
          Nat.add_le_add_right
            (advance_verticalMass_le_add_one location direction) _
        _ = verticalMass location + (directions.length + 1) := by omega

theorem advanceTime_le_period_add_one
    (location : ComplementLocation) (direction : AxisDirection) :
    advanceTime location direction ≤ location.period + 1 := by
  rcases location with ⟨horizontal, complement, vertical⟩
  cases direction with
  | east =>
      simp only [advanceTime, ComplementLocation.period]
      split <;> omega
  | north => simp [advanceTime, ComplementLocation.period]
  | west =>
      simp only [advanceTime, ComplementLocation.period]
      split <;> omega
  | south => simp [advanceTime, ComplementLocation.period]
  | invalid => simp [advanceTime, ComplementLocation.period]

theorem recordTime_le (location : ComplementLocation) :
    recordTime location ≤
      2 * location.period + 2 * verticalMass location + 5 := by
  unfold recordTime
  have horizontal := horizontal_le_period location
  have positive := signedPositive_le_verticalMass location
  omega

/-- A route suffix has a uniform per-direction bound controlled by its
initial period, vertical magnitude, and remaining direction count. -/
theorem outgoingTime_le (location : ComplementLocation)
    (directions : List AxisDirection) :
    outgoingTime location directions ≤
      4 * (directions.length + 1) *
        (location.period + verticalMass location +
          directions.length + 1) := by
  induction directions generalizing location with
  | nil =>
      simp only [outgoingTime, List.length_nil, zero_add]
      omega
  | cons direction directions induction =>
      let next := advanceComplementLocation location direction
      let scale := location.period + verticalMass location +
        (direction :: directions).length + 1
      have nextScale :
          next.period + verticalMass next + directions.length + 1 ≤
            scale := by
        simp only [next, scale, List.length_cons,
          advanceComplementLocation_period]
        have mass := advance_verticalMass_le_add_one location direction
        omega
      have rest := induction next
      have restBound :
          outgoingTime next directions ≤
            4 * (directions.length + 1) * scale := by
        exact rest.trans (Nat.mul_le_mul_left _ nextScale)
      have localBound :
          1 + recordTime location + advanceTime location direction ≤
            4 * scale := by
        have record := recordTime_le location
        have advance := advanceTime_le_period_add_one location direction
        simp only [scale, List.length_cons]
        omega
      simp only [outgoingTime]
      calc
        1 + recordTime location + advanceTime location direction +
            outgoingTime next directions ≤
          4 * scale + 4 * (directions.length + 1) * scale :=
            Nat.add_le_add localBound restBound
        _ = 4 * ((direction :: directions).length + 1) * scale := by
          simp only [List.length_cons]
          ring

/-- The complete route loop is quadratic in its finite direction word and
the unary size of its initial cursor. -/
theorem routeTime_le (location : ComplementLocation)
    (directions : List AxisDirection) :
    routeTime location directions ≤
      4 * (directions.length + 1) *
        (location.period + verticalMass location +
          directions.length + 1) := by
  cases directions with
  | nil =>
      simp only [routeTime, List.length_nil, zero_add]
      omega
  | cons direction directions =>
      let next := advanceComplementLocation location direction
      let scale := location.period + verticalMass location +
        (direction :: directions).length + 1
      have nextScale :
          next.period + verticalMass next + directions.length + 1 ≤
            scale := by
        simp only [next, scale, List.length_cons,
          advanceComplementLocation_period]
        have mass := advance_verticalMass_le_add_one location direction
        omega
      have rest := outgoingTime_le next directions
      have restBound :
          outgoingTime next directions ≤
            4 * (directions.length + 1) * scale :=
        rest.trans (Nat.mul_le_mul_left _ nextScale)
      have localBound :
          1 + advanceTime location direction ≤ 4 * scale := by
        have advance := advanceTime_le_period_add_one location direction
        simp only [scale, List.length_cons]
        omega
      simp only [routeTime]
      calc
        1 + advanceTime location direction +
            outgoingTime next directions ≤
          4 * scale + 4 * (directions.length + 1) * scale :=
            Nat.add_le_add localBound restBound
        _ = 4 * ((direction :: directions).length + 1) * scale := by
          simp only [List.length_cons]
          ring

end GadgetSparseRouteRecordMachine
end LeanTrominoes
