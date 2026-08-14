/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBivariateProgramTokenAlgebra
import LeanTrominoes.PeriodicCNFMachineProgramFields

/-!
# Bivariate templates for the bounded reset clock

Reset-clock atom numbers depend affinely on both the represented stack width
and the clock-bit position.  This file instantiates the bivariate program
language with that exact layout and proves that its emitted range, followed by
the finite-conjunction ending, is precisely the normalized clock-reset word.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace BoundedMachineBivariateClock

open Turing
open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open BivariateProgramTokenAlgebra

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- The clock bit at `position`, affine in the runtime stack width and bit
position. -/
def clockAtom : BivariateProgramTemplates.Atom where
  base := Fintype.card (Option tm.Λ) + Fintype.card tm.σ
  firstStride := BoundedMachineAtom.stackSymbolCount (tm := tm)
  secondStride := 1

@[simp]
theorem clockAtom_evaluate (space position : Nat) :
    (clockAtom (tm := tm)).evaluate space position =
      Fintype.card (Option tm.Λ) +
        (Fintype.card tm.σ +
          (space * BoundedMachineAtom.stackSymbolCount (tm := tm) +
            position)) := by
  simp [clockAtom, BivariateProgramTemplates.Atom.evaluate]
  ring

/-- One operand forcing the next value of a clock bit to zero. -/
def resetBit : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.negate
    (BivariateProgramTemplates.next (clockAtom (tm := tm)))

@[simp]
theorem evaluate_resetBit (space position : Nat) :
    (resetBit (tm := tm)).evaluate space position =
      TransitionProgram.negate
        (TransitionProgram.next
          (Fintype.card (Option tm.Λ) +
            (Fintype.card tm.σ +
              (space * BoundedMachineAtom.stackSymbolCount (tm := tm) +
                position)))) := by
  simp [resetBit]

/-- The complete unary token word for clock reset: all bit-zero operands,
then the exact right-associated conjunction ending. -/
def clockResetTokens (space clockBits : Nat) : List Token :=
  BivariateTemplateEmitterMachine.positionRangeTokens
      (resetBit (tm := tm)).recipes space 0 clockBits ++
    allEnding clockBits

theorem finRange_values (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.finRange_succ_last, List.map_append, List.map_map,
        List.range_succ]
      rw [show (Fin.val ∘ Fin.castSucc) = Fin.val by
        funext index
        rfl]
      simp [induction]

theorem positions_eq_range_map (firstPosition count : Nat) :
    positions firstPosition count =
      (List.range count).map fun offset => firstPosition + offset := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [positions_succ, List.range_succ_eq_map, induction]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro offset _
      simp only [Function.comp_apply]
      omega

theorem positions_zero_eq_range (count : Nat) :
    positions 0 count = List.range count := by
  rw [positions_eq_range_map]
  simp

theorem flatMap_positions_eq_finRange {Target : Type} (count : Nat)
    (function : Nat → List Target) :
    (positions 0 count).flatMap function =
      (List.finRange count).flatMap fun position => function position.val := by
  have values : (List.finRange count).map Fin.val = positions 0 count := by
    rw [finRange_values, positions_zero_eq_range]
  calc
    (positions 0 count).flatMap function =
        ((List.finRange count).map Fin.val).flatMap function := by rw [values]
    _ = (List.finRange count).flatMap
          (fun position => function position.val) := by
      rw [List.flatMap_map]

/-- The bivariate clock-reset stream is token-for-token the normalized
bounded-machine clock-reset program. -/
theorem clockResetTokens_eq (space clockBits : Nat) :
    clockResetTokens (tm := tm) space clockBits =
      ofProgram
        (BoundedMachineProgram.clockReset (tm := tm) (space := space)
          (clockBits := clockBits)) := by
  rw [clockResetTokens,
    BivariateProgramTokenAlgebra.positionRangeTokens_program,
    flatMap_positions_eq_finRange]
  unfold BoundedMachineProgram.clockReset BoundedMachineProgram.clockAtoms
  rw [ofProgram_all]
  simp only [List.length_map, List.length_finRange]
  congr 1
  simp only [List.flatMap_map]
  apply List.flatMap_congr
  intro position _
  rw [evaluate_resetBit]

end BoundedMachineBivariateClock
end PeriodicCNF
end LeanTrominoes
