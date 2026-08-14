/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBinarySuccessorSchedule
import LeanTrominoes.PeriodicCNFMachineBivariateClockTemplates

/-!
# Bivariate clock-successor templates

This file specializes the flat successor schedule to the bounded machine's
runtime clock atoms.  It gives fixed bivariate templates for rise, fall, and
bit equality, then defines the exact triangular token recursion that a finite
counter machine must emit and identifies it with normalized clock succession.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace BoundedMachineBivariateClockSuccessor

open Turing
open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open BoundedMachineBivariateClock

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Ordinary atom number of one runtime clock position. -/
def clockCode (space position : Nat) : Nat :=
  Fintype.card (Option tm.Λ) +
    (Fintype.card tm.σ +
      (space * BoundedMachineAtom.stackSymbolCount (tm := tm) + position))

/-- Consecutive clock atom numbers, beginning at `firstPosition`. -/
def clockCodes (space firstPosition : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      clockCode (tm := tm) space firstPosition ::
        clockCodes space (firstPosition + 1) count

@[simp]
theorem clockAtom_evaluate_eq_clockCode (space position : Nat) :
    (clockAtom (tm := tm)).evaluate space position =
      clockCode (tm := tm) space position := by
  simp [clockCode]

theorem clockCodes_eq_positions (space firstPosition count : Nat) :
    clockCodes (tm := tm) space firstPosition count =
      (positions firstPosition count).map
        (clockCode (tm := tm) space) := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [clockCodes, positions_succ, List.map_cons, induction]

@[simp]
theorem clockCodes_length (space firstPosition count : Nat) :
    (clockCodes (tm := tm) space firstPosition count).length = count := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [clockCodes, List.length_cons, induction]

/-- The normalized clock vector is exactly the consecutive bivariate atom
range at runtime `space`. -/
theorem bounded_clockAtoms_eq_clockCodes (space clockBits : Nat) :
    BoundedMachineProgram.clockAtoms (tm := tm) (space := space)
        (clockBits := clockBits) =
      clockCodes (tm := tm) space 0 clockBits := by
  rw [clockCodes_eq_positions, positions_zero_eq_range]
  unfold BoundedMachineProgram.clockAtoms
  rw [← finRange_values]
  simp only [List.map_map]
  apply List.map_congr_left
  intro position _
  simp [clockCode]

/-- Local zero-to-one branch at one clock position. -/
def rise : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.conjoin
    (BivariateProgramTemplates.negate
      (BivariateProgramTemplates.current (clockAtom (tm := tm))))
    (BivariateProgramTemplates.next (clockAtom (tm := tm)))

/-- Local one-to-zero carry branch at one clock position. -/
def fall : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.conjoin
    (BivariateProgramTemplates.current (clockAtom (tm := tm)))
    (BivariateProgramTemplates.negate
      (BivariateProgramTemplates.next (clockAtom (tm := tm))))

/-- Equality of the current and next values at one clock position. -/
def equalBit : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.equal
    (BivariateProgramTemplates.current (clockAtom (tm := tm)))
    (BivariateProgramTemplates.next (clockAtom (tm := tm)))

@[simp]
theorem evaluate_rise (space position : Nat) :
    (rise (tm := tm)).evaluate space position =
      BinarySuccessorSchedule.rise
        (clockCode (tm := tm) space position)
        (clockCode (tm := tm) space position) := by
  simp [rise, BinarySuccessorSchedule.rise, clockCode]

@[simp]
theorem evaluate_fall (space position : Nat) :
    (fall (tm := tm)).evaluate space position =
      BinarySuccessorSchedule.fall
        (clockCode (tm := tm) space position)
        (clockCode (tm := tm) space position) := by
  simp [fall, BinarySuccessorSchedule.fall, clockCode]

@[simp]
theorem evaluate_equalBit (space position : Nat) :
    (equalBit (tm := tm)).evaluate space position =
      BinarySuccessorSchedule.equalityOperand
        (clockCode (tm := tm) space position)
        (clockCode (tm := tm) space position) := by
  simp [equalBit, BinarySuccessorSchedule.equalityOperand, clockCode]

/-- Exact unary tokens of all consecutive higher-bit equality operands. -/
theorem equalityRangeTokens_eq (space firstPosition count : Nat) :
    BivariateTemplateEmitterMachine.positionRangeTokens
        (equalBit (tm := tm)).recipes space firstPosition count =
      ofProgram
        (BinarySuccessorSchedule.equalityOperands
          (clockCodes (tm := tm) space firstPosition count)
          (clockCodes (tm := tm) space firstPosition count)) := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [BivariateTemplateEmitterMachine.positionRangeTokens_succ,
        clockCodes, BinarySuccessorSchedule.equalityOperands,
        induction]
      change BivariateProgramTemplates.positionTokens
          (equalBit (tm := tm)).recipes space firstPosition ++ _ = _
      rw [BivariateProgramTemplates.Program.positionTokens_recipes,
        evaluate_equalBit, ofProgram_append]

/-- Token prefix belonging to one outer successor bit with `higherCount`
higher positions. -/
def frameTokens (space position higherCount : Nat) : List Token :=
  BivariateProgramTemplates.positionTokens (rise (tm := tm)).recipes
      space position ++
    BivariateTemplateEmitterMachine.positionRangeTokens
      (equalBit (tm := tm)).recipes space (position + 1) higherCount ++
    ofProgram (BinarySuccessorSchedule.equalityEnding higherCount) ++
    ofProgram [.conjoin] ++
    BivariateProgramTemplates.positionTokens (fall (tm := tm)).recipes
      space position

theorem frameTokens_eq (space position higherCount : Nat) :
    frameTokens (tm := tm) space position higherCount =
      ofProgram
        (BinarySuccessorSchedule.frame
          (clockCode (tm := tm) space position)
          (clockCode (tm := tm) space position)
          (clockCodes (tm := tm) space (position + 1) higherCount)
          (clockCodes (tm := tm) space (position + 1) higherCount)) := by
  unfold frameTokens BinarySuccessorSchedule.frame
  rw [BivariateProgramTemplates.Program.positionTokens_recipes,
    evaluate_rise, equalityRangeTokens_eq,
    BivariateProgramTemplates.Program.positionTokens_recipes,
    evaluate_fall]
  rw [clockCodes_length]
  simp only [ofProgram_append, List.append_assoc]

/-- Exact recursive triangular stream for `count` clock bits beginning at
`position`. -/
def tokensAux (space position : Nat) : Nat → List Token
  | 0 => ofProgram (TransitionProgram.constant false)
  | count + 1 =>
      frameTokens (tm := tm) space position count ++
        tokensAux space (position + 1) count ++
        ofProgram [.conjoin, .disjoin]

theorem tokensAux_eq (space position count : Nat) :
    tokensAux (tm := tm) space position count =
      ofProgram
        (TransitionProgram.binarySuccessor
          (clockCodes (tm := tm) space position count)
          (clockCodes (tm := tm) space position count)) := by
  induction count generalizing position with
  | zero => rfl
  | succ count induction =>
      rw [tokensAux, frameTokens_eq, induction, clockCodes,
        TransitionProgram.binarySuccessor]
      simp [BinarySuccessorSchedule.frame,
        BinarySuccessorSchedule.rise, BinarySuccessorSchedule.fall,
        BinarySuccessorSchedule.equalityEnding,
        BinarySuccessorSchedule.vectorsEqual_eq_schedule,
        TransitionProgram.conjoin, TransitionProgram.disjoin,
        ofProgram, List.append_assoc]

/-- Complete clock-successor token target for the future triangular emitter. -/
def clockSuccessorTokens (space clockBits : Nat) : List Token :=
  tokensAux (tm := tm) space 0 clockBits

/-- The triangular token target is exactly the normalized bounded-machine
clock-successor program. -/
theorem clockSuccessorTokens_eq (space clockBits : Nat) :
    clockSuccessorTokens (tm := tm) space clockBits =
      ofProgram
        (BoundedMachineProgram.clockSuccessor (tm := tm) (space := space)
          (clockBits := clockBits)) := by
  rw [clockSuccessorTokens, tokensAux_eq]
  unfold BoundedMachineProgram.clockSuccessor
  rw [bounded_clockAtoms_eq_clockCodes]

end BoundedMachineBivariateClockSuccessor
end PeriodicCNF
end LeanTrominoes
