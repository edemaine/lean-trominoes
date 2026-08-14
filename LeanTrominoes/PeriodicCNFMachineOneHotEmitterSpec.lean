/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.PeriodicCNFMachineAffineStackTemplates
import LeanTrominoes.PeriodicCNFUnaryProgramTokenAlgebra

/-!
# Concrete affine schedule for bounded one-hot fields

The fixed label and control fields are emitted literally.  One affine phase
per machine stack emits its exact-one cell program at every represented stack
position.  Separate fixed and affine closing phases then reproduce the exact
right-associated `TransitionProgram.all` suffix.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineOneHotEmitter

open BoundedMachineAtom
open AffineProgramTemplates
open AffineEmitterPipeline
open AffineTemplateEmitterMachine
open UnaryProgramTokens
open UnaryProgramTokenAlgebra

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def never {Data : Type} : Data → Bool := fun _ => false

def fixedPhase {Data : Type} (tokens : List Token) : Phase Data where
  selected := never
  recipes := []
  ending := tokens

def affinePhase {Data : Type} (selected : Data → Bool)
    (program : AffineProgramTemplates.Program) : Phase Data where
  selected := selected
  recipes := program.recipes
  ending := []

@[simp]
theorem positionRangeTokens_nil (firstPosition count : Nat) :
    positionRangeTokens [] firstPosition count = [] := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [positionRangeTokens_succ, positionTokens]
      simp [induction]

@[simp]
theorem fixedPhase_emitted {Data : Type} (tokens : List Token)
    (data : List Data) :
    (fixedPhase tokens : Phase Data).emitted data = tokens := by
  simp [fixedPhase, Phase.emitted]

theorem affinePhase_emitted {Data : Type} (selected : Data → Bool)
    (program : AffineProgramTemplates.Program) (data : List Data)
    (count : Nat)
    (countEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      count) :
    (affinePhase selected program).emitted data =
      (positions 0 count).flatMap fun position =>
        ofProgram (program.evaluate position) := by
  unfold affinePhase Phase.emitted
  rw [countEq, positionRangeTokens_program]
  simp

@[simp]
theorem emittedAll_append {Data : Type} (first second : List (Phase Data))
    (data : List Data) :
    emittedAll (first ++ second) data =
      emittedAll first data ++ emittedAll second data := by
  induction first with
  | nil => rfl
  | cons phase first induction =>
      simp [emittedAll, induction, List.append_assoc]

theorem emittedAll_map {Data Index : Type} (indices : List Index)
    (phase : Index → Phase Data) (data : List Data) :
    emittedAll (indices.map phase) data =
      indices.flatMap fun index => (phase index).emitted data := by
  induction indices with
  | nil => rfl
  | cons index indices induction => simp [emittedAll, induction]

theorem positions_eq_range_map (firstPosition count : Nat) :
    positions firstPosition count =
      (List.range count).map fun offset => firstPosition + offset := by
  induction count generalizing firstPosition with
  | zero => rfl
  | succ count induction =>
      rw [positions_succ, List.range_succ_eq_map, List.map_cons,
        induction]
      simp only [Nat.add_zero, List.map_map]
      congr 1
      apply List.map_congr_left
      intro offset _
      simp only [Function.comp_apply]
      omega

theorem positions_zero_eq_range (count : Nat) :
    positions 0 count = List.range count := by
  rw [positions_eq_range_map]
  simp

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

def stackCellPhase {Data : Type} (selected : Data → Bool)
    (stack : tm.K) : Phase Data :=
  affinePhase selected
    (BoundedMachineAffineProgram.stackCellExactlyOne (tm := tm) stack)

def conjoinPhase {Data : Type} (selected : Data → Bool) : Phase Data :=
  affinePhase selected [.conjoin]

def fixedOperandTokens : List Token :=
  ofProgram (BoundedMachineProgram.labelExactlyOne (tm := tm)) ++
    ofProgram (BoundedMachineProgram.stateExactlyOne (tm := tm))

/-- Fixed phase schedule for the complete one-hot program.  Runtime stack
width enters only through `selected`. -/
def phases {Data : Type} (selected : Data → Bool) : List (Phase Data) :=
  [fixedPhase (fixedOperandTokens (tm := tm))] ++
    (finiteValues tm.K).map (stackCellPhase (tm := tm) selected) ++
    [fixedPhase (allEnding 2)] ++
    (finiteValues tm.K).map (fun _ => conjoinPhase selected)

def repeatInstructionTokens (instruction : TransitionInstruction) :
    Nat → List Token
  | 0 => []
  | count + 1 => instructionTokens instruction ++
      repeatInstructionTokens instruction count

theorem repeatInstructionTokens_succ_right
    (instruction : TransitionInstruction) (count : Nat) :
    repeatInstructionTokens instruction (count + 1) =
      repeatInstructionTokens instruction count ++
        instructionTokens instruction := by
  induction count with
  | zero => simp [repeatInstructionTokens]
  | succ count induction =>
      change instructionTokens instruction ++
          repeatInstructionTokens instruction (count + 1) =
        (instructionTokens instruction ++
          repeatInstructionTokens instruction count) ++
            instructionTokens instruction
      rw [induction, List.append_assoc]

theorem foldEnding_add (emptyValue : Bool)
    (operator : TransitionInstruction) (first second : Nat) :
    foldEnding emptyValue operator (first + second) =
      foldEnding emptyValue operator first ++
        repeatInstructionTokens operator second := by
  induction second with
  | zero => simp [repeatInstructionTokens]
  | succ second induction =>
      rw [Nat.add_succ, foldEnding, induction,
        repeatInstructionTokens_succ_right, List.append_assoc]

theorem repeatInstructionTokens_add (instruction : TransitionInstruction)
    (first second : Nat) :
    repeatInstructionTokens instruction (first + second) =
      repeatInstructionTokens instruction first ++
        repeatInstructionTokens instruction second := by
  induction first with
  | zero => simp [repeatInstructionTokens]
  | succ first induction =>
      simp [Nat.succ_add, repeatInstructionTokens, induction,
        List.append_assoc]

theorem flatMap_positions_constant (instruction : TransitionInstruction)
    (count : Nat) :
    (positions 0 count).flatMap (fun _ => ofProgram [instruction]) =
      repeatInstructionTokens instruction count := by
  rw [positions_zero_eq_range]
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        induction, repeatInstructionTokens_succ_right]
      simp [ofProgram]

theorem flatMap_constant_repeat {Index : Type} (indices : List Index)
    (instruction : TransitionInstruction) (count : Nat) :
    indices.flatMap (fun _ => repeatInstructionTokens instruction count) =
      repeatInstructionTokens instruction (indices.length * count) := by
  induction indices with
  | nil => simp [repeatInstructionTokens]
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.length_cons]
      rw [induction, show (indices.length + 1) * count =
          count + indices.length * count by ring,
        repeatInstructionTokens_add]

theorem flatMap_flatMap {First Second Third : Type}
    (items : List First) (middle : First → List Second)
    (last : Second → List Third) :
    (items.flatMap middle).flatMap last =
      items.flatMap fun item => (middle item).flatMap last := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp [List.flatMap_append, induction]

theorem sum_map_constant {Index : Type} (indices : List Index)
    (value : Nat) :
    (indices.map fun _ => value).sum = indices.length * value := by
  induction indices with
  | nil => simp
  | cons index indices induction =>
      rw [List.map_cons, List.sum_cons, induction, List.length_cons]
      ring

theorem stackCellPhase_emitted {Data : Type} (selected : Data → Bool)
    (stack : tm.K) (data : List Data) (space : Nat)
    (countEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    (stackCellPhase (tm := tm) selected stack).emitted data =
      (List.finRange space).flatMap fun position =>
        ofProgram
          (BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
            position.val) := by
  rw [stackCellPhase, affinePhase_emitted selected _ data space countEq]
  rw [flatMap_positions_eq_finRange]
  apply List.flatMap_congr
  intro position _
  rw [BoundedMachineAffineProgram.evaluate_stackCellExactlyOne]

theorem conjoinPhase_emitted {Data : Type} (selected : Data → Bool)
    (data : List Data) (space : Nat)
    (countEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    (conjoinPhase selected).emitted data =
      repeatInstructionTokens .conjoin space := by
  rw [conjoinPhase, affinePhase_emitted selected _ data space countEq]
  exact flatMap_positions_constant .conjoin space

theorem emittedAll_phases {Data : Type} (selected : Data → Bool)
    (data : List Data) (space : Nat)
    (countEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (phases (tm := tm) selected) data =
      ofProgram
        (BoundedMachineProgram.oneHotFields (tm := tm) (space := space)) := by
  have schedule : emittedAll (phases (tm := tm) selected) data =
      fixedOperandTokens (tm := tm) ++
        (finiteValues tm.K).flatMap (fun stack =>
          (List.finRange space).flatMap fun position =>
            ofProgram
              (BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
                position.val)) ++
        allEnding 2 ++
        (finiteValues tm.K).flatMap fun _ =>
          repeatInstructionTokens .conjoin space := by
    unfold phases
    simp only [emittedAll_append, emittedAll, fixedPhase_emitted,
      List.append_nil]
    rw [emittedAll_map, emittedAll_map]
    simp only [stackCellPhase_emitted selected _ data space countEq,
      conjoinPhase_emitted selected data space countEq]
  have stackTokens :
      (finiteValues tm.K).flatMap (fun stack =>
          (List.finRange space).flatMap fun position =>
            ofProgram
              (BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
                position.val)) =
        ((finiteValues tm.K).flatMap fun stack =>
          (List.finRange space).map fun position =>
            BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
              position.val).flatMap ofProgram := by
    rw [flatMap_flatMap]
    apply List.flatMap_congr
    intro stack _
    rw [List.flatMap_map]
  have operandLength :
      (BoundedMachineProgram.oneHotFieldPrograms (tm := tm)
        (space := space)).length = 2 + Fintype.card tm.K * space := by
    simp [BoundedMachineProgram.oneHotFieldPrograms,
      List.length_flatMap, finiteValues_length]
    omega
  have closers :
      (finiteValues tm.K).flatMap (fun _ =>
          repeatInstructionTokens .conjoin space) =
        repeatInstructionTokens .conjoin (Fintype.card tm.K * space) := by
    rw [flatMap_constant_repeat, finiteValues_length]
  have allEndingSplit :
      allEnding (2 + Fintype.card tm.K * space) =
        allEnding 2 ++
          repeatInstructionTokens .conjoin (Fintype.card tm.K * space) :=
    foldEnding_add true .conjoin 2 (Fintype.card tm.K * space)
  rw [schedule, BoundedMachineProgram.oneHotFields, ofProgram_all,
    operandLength, allEndingSplit, stackTokens, closers]
  unfold BoundedMachineProgram.oneHotFieldPrograms fixedOperandTokens
  simp [List.append_assoc]

end BoundedMachineOneHotEmitter
end PeriodicCNF
end LeanTrominoes
