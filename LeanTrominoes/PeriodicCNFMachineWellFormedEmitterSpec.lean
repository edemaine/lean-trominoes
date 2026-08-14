/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec
import LeanTrominoes.SelectedPrefixMarkerTime

/-!
# Concrete emitter schedule for bounded well-formedness

Prefix tags provide the exact `space - 1` loop used by occupied-prefix
constraints.  For each stack, an affine interior phase is followed by the
literal terminal constant-true boundary.  The resulting suffix schedule and
the existing one-hot schedule emit `wellFormedFields` exactly.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineWellFormedEmitter

open BoundedMachineAtom
open AffineProgramTemplates
open AffineEmitterPipeline
open UnaryProgramTokens
open UnaryProgramTokenAlgebra
open SelectedPrefixMarkerMachine
open BoundedMachineOneHotEmitter

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

abbrev Marked (cutoff : Nat) (Data : Type) := Tagged cutoff Data

def fullSelector {Data : Type} {cutoff : Nat} (selected : Data → Bool) :
    Marked cutoff Data → Bool :=
  afterPrefix selected 0

def interiorSelector {Data : Type} {cutoff : Nat}
    (selected : Data → Bool) :
    Marked cutoff Data → Bool :=
  afterPrefix selected 1

def suffixInteriorPhase {Data : Type} {cutoff : Nat}
    (selected : Data → Bool)
    (stack : tm.K) : Phase (Marked cutoff Data) :=
  affinePhase (interiorSelector selected)
    (BoundedMachineAffineProgram.stackSuffixInterior (tm := tm) stack)

def terminalSuffixPhase {Data : Type} {cutoff : Nat} :
    Phase (Marked cutoff Data) :=
  fixedPhase (ofProgram (TransitionProgram.constant true))

def stackSuffixOperandPhases {Data : Type} {cutoff : Nat}
    (selected : Data → Bool)
    (stack : tm.K) : List (Phase (Marked cutoff Data)) :=
  [suffixInteriorPhase (tm := tm) selected stack, terminalSuffixPhase]

/-- Complete phase list for `stackSuffixFields`. -/
def suffixPhases {Data : Type} {cutoff : Nat} (selected : Data → Bool) :
    List (Phase (Marked cutoff Data)) :=
  (finiteValues tm.K).flatMap
      (stackSuffixOperandPhases (tm := tm) selected) ++
    [fixedPhase (allEnding 0)] ++
    (finiteValues tm.K).map (fun _ =>
      conjoinPhase (fullSelector selected))

theorem fullSelector_count {Data : Type} (selected : Data → Bool)
    (cutoff : Nat) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount (fullSelector selected)
        (mark selected cutoff data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data := by
  simpa [fullSelector] using
    selectedCount_afterPrefix_mark selected (cutoff := cutoff)
      (skip := 0) (Nat.zero_le cutoff) data

theorem interiorSelector_count {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (cutoffPositive : 1 ≤ cutoff) (data : List Data) :
    UnaryPolynomialPaddingMachine.selectedCount (interiorSelector selected)
        (mark selected cutoff data) =
      UnaryPolynomialPaddingMachine.selectedCount selected data - 1 := by
  simpa [interiorSelector] using
    selectedCount_afterPrefix_mark selected (cutoff := cutoff)
      (skip := 1) cutoffPositive data

theorem range_pred_append_last {space : Nat} (positive : 0 < space) :
    List.range space = List.range (space - 1) ++ [space - 1] := by
  obtain ⟨space, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : space ≠ 0)
  simp [List.range_succ]

theorem suffixInteriorPhase_emitted {Data : Type}
    (selected : Data → Bool) {cutoff : Nat}
    (cutoffPositive : 1 ≤ cutoff) (stack : tm.K) (data : List Data)
    (space : Nat)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    (suffixInteriorPhase (tm := tm) (cutoff := cutoff) selected stack).emitted
        (mark selected cutoff data) =
      (List.range (space - 1)).flatMap fun position =>
        ofProgram
          (BoundedMachineProgram.stackSuffixExpression (tm := tm)
            (space := space) stack position) := by
  rw [suffixInteriorPhase,
    affinePhase_emitted (interiorSelector selected) _
      (mark selected cutoff data) (space - 1)]
  · rw [positions_zero_eq_range]
    apply List.flatMap_congr
    intro position member
    rw [BoundedMachineAffineProgram.evaluate_stackSuffixInterior_eq]
    have positionLt : position < space - 1 := List.mem_range.mp member
    omega
  · rw [interiorSelector_count selected cutoffPositive, spaceEq]

theorem emitted_stackSuffixOperandPhases {Data : Type}
    (selected : Data → Bool) {cutoff : Nat}
    (cutoffPositive : 1 ≤ cutoff) (stack : tm.K) (data : List Data)
    (space : Nat) (spacePositive : 0 < space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll
        (stackSuffixOperandPhases (tm := tm) (cutoff := cutoff)
          selected stack)
        (mark selected cutoff data) =
      (BoundedMachineProgram.stackSuffixExpressions (tm := tm)
        (space := space) stack).flatMap ofProgram := by
  unfold stackSuffixOperandPhases terminalSuffixPhase
  simp only [emittedAll, List.append_nil]
  rw [suffixInteriorPhase_emitted selected cutoffPositive stack data space
    spaceEq, fixedPhase_emitted]
  unfold BoundedMachineProgram.stackSuffixExpressions
  have rangeEq := range_pred_append_last spacePositive
  conv_rhs => rw [rangeEq]
  rw [List.map_append, List.flatMap_append]
  simp only [List.map_singleton, List.flatMap_singleton]
  congr 1
  · rw [List.flatMap_map]
  · unfold BoundedMachineProgram.stackSuffixExpression
    rw [if_neg (by omega)]

theorem emittedAll_flatMap {Data Index : Type} (indices : List Index)
    (phase : Index → List (Phase Data)) (data : List Data) :
    emittedAll (indices.flatMap phase) data =
      indices.flatMap fun index => emittedAll (phase index) data := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      rw [List.flatMap_cons, emittedAll_append, induction,
        List.flatMap_cons]

theorem emittedAll_suffixPhases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (cutoffPositive : 1 ≤ cutoff) (data : List Data)
    (space : Nat) (spacePositive : 0 < space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (suffixPhases (tm := tm) (cutoff := cutoff) selected)
        (mark selected cutoff data) =
      ofProgram
        (BoundedMachineProgram.stackSuffixFields (tm := tm)
          (space := space)) := by
  have fullCount :
      UnaryPolynomialPaddingMachine.selectedCount (fullSelector selected)
          (mark selected cutoff data) = space := by
    rw [fullSelector_count, spaceEq]
  have operands : emittedAll
      ((finiteValues tm.K).flatMap
        (stackSuffixOperandPhases (tm := tm) (cutoff := cutoff) selected))
      (mark selected cutoff data) =
      (BoundedMachineProgram.allStackSuffixExpressions (tm := tm)
        (space := space)).flatMap ofProgram := by
    rw [emittedAll_flatMap]
    unfold BoundedMachineProgram.allStackSuffixExpressions
    rw [BoundedMachineOneHotEmitter.flatMap_flatMap]
    apply List.flatMap_congr
    intro stack _
    exact emitted_stackSuffixOperandPhases selected cutoffPositive stack data
      space spacePositive spaceEq
  have closing : emittedAll
      ((finiteValues tm.K).map (fun _ =>
        conjoinPhase (fullSelector selected)))
      (mark selected cutoff data) =
      repeatInstructionTokens .conjoin (Fintype.card tm.K * space) := by
    rw [emittedAll_map]
    simp only [conjoinPhase_emitted (fullSelector selected)
      (mark selected cutoff data) space fullCount]
    rw [flatMap_constant_repeat, finiteValues_length]
  have operandLength :
      (BoundedMachineProgram.allStackSuffixExpressions (tm := tm)
        (space := space)).length = Fintype.card tm.K * space := by
    simp [BoundedMachineProgram.allStackSuffixExpressions,
      BoundedMachineProgram.stackSuffixExpressions,
      List.length_flatMap, finiteValues_length]
  have endingSplit :
      allEnding (Fintype.card tm.K * space) =
        allEnding 0 ++
          repeatInstructionTokens .conjoin (Fintype.card tm.K * space) :=
    by
      simpa [allEnding] using
        foldEnding_add true .conjoin 0 (Fintype.card tm.K * space)
  unfold suffixPhases
  rw [emittedAll_append, emittedAll_append, operands]
  simp only [emittedAll, fixedPhase_emitted, List.append_nil]
  rw [closing]
  unfold BoundedMachineProgram.stackSuffixFields
  rw [ofProgram_all, operandLength, endingSplit]
  rw [List.append_assoc]

/-- Complete phase list for structural well-formedness. -/
def phases {Data : Type} {cutoff : Nat} (selected : Data → Bool) :
    List (Phase (Marked cutoff Data)) :=
  BoundedMachineOneHotEmitter.phases (tm := tm) (fullSelector selected) ++
    suffixPhases (tm := tm) selected ++
    [fixedPhase (instructionTokens .conjoin)]

theorem emittedAll_phases {Data : Type} (selected : Data → Bool)
    {cutoff : Nat} (cutoffPositive : 1 ≤ cutoff) (data : List Data)
    (space : Nat) (spacePositive : 0 < space)
    (spaceEq : UnaryPolynomialPaddingMachine.selectedCount selected data =
      space) :
    emittedAll (phases (tm := tm) (cutoff := cutoff) selected)
        (mark selected cutoff data) =
      ofProgram
        (BoundedMachineProgram.wellFormedFields (tm := tm)
          (space := space)) := by
  have fullCount :
      UnaryPolynomialPaddingMachine.selectedCount (fullSelector selected)
          (mark selected cutoff data) = space := by
    rw [fullSelector_count, spaceEq]
  unfold phases
  rw [emittedAll_append, emittedAll_append,
    BoundedMachineOneHotEmitter.emittedAll_phases
      (fullSelector selected) (mark selected cutoff data) space fullCount,
    emittedAll_suffixPhases selected cutoffPositive data space spacePositive
      spaceEq]
  simp only [emittedAll, fixedPhase_emitted, List.append_nil]
  unfold BoundedMachineProgram.wellFormedFields
  rw [ofProgram_conjoin]

end BoundedMachineWellFormedEmitter
end PeriodicCNF
end LeanTrominoes
