/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalColumnData

/-! # Semantics of packed carrier-span terminal columns -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierPackedSpanTerminalColumns

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanRouteTailRecords

@[simp] theorem hasUnit_unaryField_zero :
    hasUnit (UnaryFieldEncoderMachine.unaryField 0) = false := by
  rfl

@[simp] theorem hasUnit_unaryField_succ (value : Nat) :
    hasUnit (UnaryFieldEncoderMachine.unaryField (value + 1)) = true := by
  simp [hasUnit, UnaryFieldEncoderMachine.unaryField,
    List.replicate_succ]

@[simp] theorem directionRankBlockOutput_unaryField_zero :
    directionRankBlockOutput
        (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  simp [directionRankBlockOutput, guardedDirectionCandidate,
    SeparatedBooleanGuard.guarded]

/-- The packed residue selects the exact four carrier direction ranks. -/
theorem directionRankBlockOutput_unaryField_packed
    (horizontal nextSlice : Bool) (span : Nat) :
    directionRankBlockOutput
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 +
            2 * BooleanListUnaryFields.bitNat horizontal +
              BooleanListUnaryFields.bitNat nextSlice)) =
      UnaryFieldEncoderMachine.unaryFields
        (terminalDataDirectionRanks
          (carrierLensRouteTerminalDataBlock horizontal span)) := by
  have positive : 0 <
      4 * span + 4 +
        2 * BooleanListUnaryFields.bitNat horizontal +
          BooleanListUnaryFields.bitNat nextSlice := by
    omega
  have unit :
      hasUnit
          (UnaryFieldEncoderMachine.unaryField
            (4 * span + 4 +
              2 * BooleanListUnaryFields.bitNat horizontal +
                BooleanListUnaryFields.bitNat nextSlice)) = true := by
    obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt positive)
    rw [valueEq]
    exact hasUnit_unaryField_succ value
  have residue (target : Residue) :
      hasResidue target
          (UnaryFieldEncoderMachine.unaryField
            (4 * span + 4 +
              2 * BooleanListUnaryFields.bitNat horizontal +
                BooleanListUnaryFields.bitNat nextSlice)) =
        (metadataResidue horizontal nextSlice == target) := by
    have codeEq :
        2 * BooleanListUnaryFields.bitNat horizontal +
            BooleanListUnaryFields.bitNat nextSlice =
          (metadataResidue horizontal nextSlice).code := by
      cases horizontal <;> cases nextSlice <;> rfl
    rw [show
        4 * span + 4 +
            2 * BooleanListUnaryFields.bitNat horizontal +
              BooleanListUnaryFields.bitNat nextSlice =
          4 * span + 4 +
            (2 * BooleanListUnaryFields.bitNat horizontal +
              BooleanListUnaryFields.bitNat nextSlice) by omega,
      codeEq]
    exact hasResidue_unaryField_packed target
      (metadataResidue horizontal nextSlice) span
  unfold directionRankBlockOutput guardedDirectionCandidate
  rw [unit, residue .zero, residue .one, residue .two, residue .three]
  rw [carrierLensRouteTerminalDataBlock_directionRanks]
  cases horizontal <;> cases nextSlice <;>
    rfl

/-- Removing eight units from a sufficiently long unary field subtracts
eight from its represented value. -/
theorem drop_eight_unaryField
    (value : Nat) (large : 8 ≤ value) :
    (UnaryFieldEncoderMachine.unaryField value).drop 8 =
      UnaryFieldEncoderMachine.unaryField (value - 8) := by
  obtain ⟨tail, rfl⟩ := Nat.exists_eq_add_of_le large
  simp [UnaryFieldEncoderMachine.unaryField,
    List.replicate_add]

@[simp] theorem radialLengthBlockOutput_unaryField_zero :
    radialLengthBlockOutput
        (UnaryFieldEncoderMachine.unaryField 0) = [] := by
  simp [radialLengthBlockOutput, SeparatedBooleanGuard.guarded]

/-- A positive packed carrier span decodes to its exact four radial
lengths. -/
theorem radialLengthBlockOutput_unaryField_packed
    (horizontal nextSlice : Bool) (span : Nat) (large : 6 < span) :
    radialLengthBlockOutput
        (UnaryFieldEncoderMachine.unaryField
          (4 * span + 4 +
            2 * BooleanListUnaryFields.bitNat horizontal +
              BooleanListUnaryFields.bitNat nextSlice)) =
      UnaryFieldEncoderMachine.unaryFields
        (terminalDataRadialLengths
          (carrierLensRouteTerminalDataBlock horizontal span)) := by
  have positive : 0 <
      4 * span + 4 +
        2 * BooleanListUnaryFields.bitNat horizontal +
          BooleanListUnaryFields.bitNat nextSlice := by
    omega
  have unit :
      hasUnit
          (UnaryFieldEncoderMachine.unaryField
            (4 * span + 4 +
              2 * BooleanListUnaryFields.bitNat horizontal +
                BooleanListUnaryFields.bitNat nextSlice)) = true := by
    obtain ⟨value, valueEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt positive)
    rw [valueEq]
    exact hasUnit_unaryField_succ value
  unfold radialLengthBlockOutput SeparatedBooleanGuard.guarded
  rw [unit]
  unfold radialLengthCandidate
  have residueCode : ∃ residue : Residue,
      2 * BooleanListUnaryFields.bitNat horizontal +
          BooleanListUnaryFields.bitNat nextSlice = residue.code := by
    exact ⟨metadataResidue horizontal nextSlice, by
      cases horizontal <;> cases nextSlice <;> rfl⟩
  rcases residueCode with ⟨residue, residueCode⟩
  rw [show
      4 * span + 4 +
          2 * BooleanListUnaryFields.bitNat horizontal +
            BooleanListUnaryFields.bitNat nextSlice =
        4 * span + 4 + residue.code by omega]
  rw [reducedOutput_unaryField_packed span residue]
  rw [drop_eight_unaryField (span + 2) (by omega)]
  rw [carrierLensRouteTerminalDataBlock_radialLengths]
  have terminalLengthEq :
      ((span : Int) - 6).toNat = span - 6 := by
    omega
  rw [terminalLengthEq]
  rw [show span + 2 - 8 = span - 6 by omega]
  simp [UnaryFieldEncoderMachine.unaryFields_cons]

end CarrierPackedSpanTerminalColumns
end LeanTrominoes.PeriodicOrthocrossing
