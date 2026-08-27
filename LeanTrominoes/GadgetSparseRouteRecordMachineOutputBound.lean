/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteRecordMachinePotential

/-! # Output-length bounds for the complement-counter route machine -/

namespace LeanTrominoes

namespace GadgetSparseRouteRecordMachine

open PeriodicCNFStripReduction
open PeriodicCNFStripReduction.RouteRasterRequest

@[simp] theorem assignmentTokens_location_length
    (location : ComplementLocation)
    (cellType : Gadget.OrthogonalCellType) :
    (GadgetSparseAssignmentTokens.assignmentTokens
      (location.toNatHorizontal.toCell, cellType)).length =
        location.horizontal + signedPositive location.vertical + 2 := by
  rcases location with ⟨horizontal, complement, vertical⟩
  simp [GadgetSparseAssignmentTokens.assignmentTokens,
    ComplementLocation.toNatHorizontal, NatHorizontalLocation.toCell,
    signedPositive]
  omega

/-- Every emitted record is charged to one remaining direction and the
initial cursor potential. -/
theorem outgoingBlocks_length_le (color : Gadget.WireColor)
    (location : ComplementLocation) (incoming : AxisDirection)
    (directions : List AxisDirection) :
    (outgoingBlocks color location incoming directions).length ≤
      directions.length *
        (location.period + verticalMass location +
          directions.length + 2) := by
  induction directions generalizing location incoming with
  | nil => simp [outgoingBlocks]
  | cons outgoing directions induction =>
      let next := advanceComplementLocation location outgoing
      let scale := location.period + verticalMass location +
        (outgoing :: directions).length + 2
      have nextScale :
          next.period + verticalMass next + directions.length + 2 ≤
            scale := by
        simp only [next, scale, List.length_cons,
          advanceComplementLocation_period]
        have mass := advance_verticalMass_le_add_one location outgoing
        omega
      have rest := induction next outgoing
      have restBound :
          (outgoingBlocks color next outgoing directions).length ≤
            directions.length * scale :=
        rest.trans (Nat.mul_le_mul_left _ nextScale)
      have recordBound :
          (GadgetSparseAssignmentTokens.assignmentTokens
            (location.toNatHorizontal.toCell,
              routingCellTypeFromForwardDirections
                incoming outgoing color)).length ≤ scale := by
        rw [assignmentTokens_location_length]
        have horizontal := horizontal_le_period location
        have positive := signedPositive_le_verticalMass location
        simp only [scale, List.length_cons]
        omega
      simp only [outgoingBlocks, List.length_append]
      calc
        (GadgetSparseAssignmentTokens.assignmentTokens
              (location.toNatHorizontal.toCell,
                routingCellTypeFromForwardDirections
                  incoming outgoing color)).length +
            (outgoingBlocks color next outgoing directions).length ≤
          scale + directions.length * scale :=
            Nat.add_le_add recordBound restBound
        _ = (outgoing :: directions).length * scale := by
          simp only [List.length_cons]
          ring

/-- The complete record word is quadratic in the direction count and the
initial unary cursor potential. -/
theorem sparseRouteRecordBlocks_length_le (color : Gadget.WireColor)
    (location : ComplementLocation) (directions : List AxisDirection) :
    (sparseRouteRecordBlocksFromComplementDirections
      color location directions).length ≤
        directions.length *
          (location.period + verticalMass location +
            directions.length + 2) := by
  cases directions with
  | nil => simp [sparseRouteRecordBlocksFromComplementDirections]
  | cons incoming directions =>
      let next := advanceComplementLocation location incoming
      have nextScale :
          next.period + verticalMass next + directions.length + 2 ≤
            location.period + verticalMass location +
              (incoming :: directions).length + 2 := by
        simp only [next, List.length_cons,
          advanceComplementLocation_period]
        have mass := advance_verticalMass_le_add_one location incoming
        omega
      rw [← outgoingBlocks_eq_sparseRouteRecordBlocks]
      exact (outgoingBlocks_length_le color next incoming directions).trans
        (Nat.mul_le_mul (by simp) nextScale)

theorem complementRecordBlock_length_le (request : Request) :
    (complementRecordBlock request).length ≤
      (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
        request.normalization).directions.length *
        (request.metadata.complementLocation.period +
          verticalMass request.metadata.complementLocation +
          (PeriodicThreeDM.NormalizationDirectionRequest.normalizeThreeRounds
            request.normalization).directions.length + 2) := by
  unfold complementRecordBlock
  exact sparseRouteRecordBlocks_length_le _ _ _

end GadgetSparseRouteRecordMachine
end LeanTrominoes
