/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramFields

/-!
# Normalized postorder programs for bounded-slice well-formedness

The structural prefix of the bounded reset-clock relation consists of one-hot
finite fields and the occupied-prefix constraint for every bounded stack.
This file presents both parts directly as flat postorder programs over the
affine atom layout and proves exact agreement with their semantic expression
definitions.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineProgram

open BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def labelExactlyOne : TransitionProgram.Program :=
  TransitionProgram.currentExactlyOne (labelAtoms (tm := tm))

def stateExactlyOne : TransitionProgram.Program :=
  TransitionProgram.currentExactlyOne (stateAtoms (tm := tm))

def stackCellExactlyOne (stack : tm.K) (position : Nat) :
    TransitionProgram.Program :=
  TransitionProgram.currentExactlyOne
    (stackCellAtoms (tm := tm) stack position)

@[simp]
theorem program_labelExactlyOne :
    (TransitionExpr.currentExactlyOne
      (BoundedMachineAtom.labelAtoms (tm := tm) (space := space)
        (clockBits := clockBits))).program = labelExactlyOne (tm := tm) := by
  simp only [TransitionExpr.program_currentExactlyOne, labelExactlyOne]
  rw [← labelAtoms_eq (tm := tm) (space := space)
    (clockBits := clockBits)]

@[simp]
theorem program_stateExactlyOne :
    (TransitionExpr.currentExactlyOne
      (BoundedMachineAtom.stateAtoms (tm := tm) (space := space)
        (clockBits := clockBits))).program = stateExactlyOne (tm := tm) := by
  simp only [TransitionExpr.program_currentExactlyOne, stateExactlyOne]
  rw [← stateAtoms_eq (tm := tm) (space := space)
    (clockBits := clockBits)]

@[simp]
theorem program_stackCellExactlyOne (stack : tm.K) (position : Fin space) :
    (TransitionExpr.currentExactlyOne
      (BoundedMachineAtom.stackCellAtoms (tm := tm)
        (clockBits := clockBits) stack position)).program =
      stackCellExactlyOne (tm := tm) stack position.val := by
  simp only [TransitionExpr.program_currentExactlyOne, stackCellExactlyOne]
  rw [← stackCellAtoms_eq (tm := tm) (clockBits := clockBits) stack
    position]

/-- Direct postorder programs for every finite one-hot field. -/
def oneHotFieldPrograms : List TransitionProgram.Program :=
  [labelExactlyOne (tm := tm), stateExactlyOne (tm := tm)] ++
    (finiteValues tm.K).flatMap fun stack =>
      (List.finRange space).map fun position =>
        stackCellExactlyOne (tm := tm) stack position.val

/-- Complete one-hot well-formedness program. -/
def oneHotFields : TransitionProgram.Program :=
  TransitionProgram.all
    (oneHotFieldPrograms (tm := tm) (space := space))

@[simp]
theorem map_program_oneHotFieldExpressions :
    (BoundedMachineAtom.oneHotFieldExpressions (tm := tm) (space := space)
      (clockBits := clockBits)).map TransitionExpr.program =
        oneHotFieldPrograms (tm := tm) (space := space) := by
  simp only [BoundedMachineAtom.oneHotFieldExpressions,
    oneHotFieldPrograms, List.map_append, List.map_cons, List.map_nil,
    List.map_flatMap, program_labelExactlyOne, program_stateExactlyOne]
  congr 1
  apply List.flatMap_congr
  intro stack _
  simp only [List.map_map]
  apply List.map_congr_left
  intro position _
  exact program_stackCellExactlyOne (tm := tm) (clockBits := clockBits)
    stack position

@[simp]
theorem program_oneHotFields :
    (BoundedMachineAtom.oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        oneHotFields (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.oneHotFields, oneHotFields]

/-- Affine atom selecting the unused value of one bounded stack cell. -/
def stackNoneAtom (stack : tm.K) (position : Nat) : Nat :=
  Fintype.card (Option tm.Λ) +
    (Fintype.card tm.σ +
      (stackSymbolCode ⟨stack, none⟩ +
        BoundedMachineAtom.stackSymbolCount (tm := tm) * position))

@[simp]
theorem stackNoneAtom_eq (stack : tm.K) (position : Fin space) :
    stackNoneAtom (tm := tm) stack position.val =
      BoundedMachineAtom.stackNoneAtom (tm := tm)
        (clockBits := clockBits) stack position := by
  simp [stackNoneAtom, BoundedMachineAtom.stackNoneAtom,
    BoundedMachineAtom.code_stack]

/-- One adjacent occupied-prefix constraint, directly in postorder. -/
def stackSuffixExpression (stack : tm.K) (index : Nat) :
    TransitionProgram.Program :=
  if index + 1 < space then
    TransitionProgram.disjoin
      (TransitionProgram.negate
        (TransitionProgram.current
          (stackNoneAtom (tm := tm) stack index)))
      (TransitionProgram.current
        (stackNoneAtom (tm := tm) stack (index + 1)))
  else
    TransitionProgram.constant true

@[simp]
theorem program_stackSuffixExpression (stack : tm.K) (index : Nat) :
    (BoundedMachineAtom.stackSuffixExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack index).program =
        stackSuffixExpression (tm := tm) (space := space) stack index := by
  unfold BoundedMachineAtom.stackSuffixExpression stackSuffixExpression
  split <;> simp [stackNoneAtom, BoundedMachineAtom.stackNoneAtom,
    BoundedMachineAtom.code_stack]

def stackSuffixExpressions (stack : tm.K) :
    List TransitionProgram.Program :=
  (List.range space).map
    (stackSuffixExpression (tm := tm) (space := space) stack)

def allStackSuffixExpressions : List TransitionProgram.Program :=
  (finiteValues tm.K).flatMap
    (stackSuffixExpressions (tm := tm) (space := space))

def stackSuffixFields : TransitionProgram.Program :=
  TransitionProgram.all
    (allStackSuffixExpressions (tm := tm) (space := space))

@[simp]
theorem map_program_stackSuffixExpressions (stack : tm.K) :
    (BoundedMachineAtom.stackSuffixExpressions (tm := tm) (space := space)
      (clockBits := clockBits) stack).map TransitionExpr.program =
        stackSuffixExpressions (tm := tm) (space := space) stack := by
  simp [BoundedMachineAtom.stackSuffixExpressions, stackSuffixExpressions,
    List.map_map, Function.comp_def]

@[simp]
theorem map_program_allStackSuffixExpressions :
    (BoundedMachineAtom.allStackSuffixExpressions (tm := tm)
      (space := space) (clockBits := clockBits)).map TransitionExpr.program =
        allStackSuffixExpressions (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.allStackSuffixExpressions,
    allStackSuffixExpressions, List.map_flatMap]

@[simp]
theorem program_stackSuffixFields :
    (BoundedMachineAtom.stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        stackSuffixFields (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.stackSuffixFields, stackSuffixFields]

/-- Complete bounded-slice structural well-formedness program. -/
def wellFormedFields : TransitionProgram.Program :=
  TransitionProgram.conjoin
    (oneHotFields (tm := tm) (space := space))
    (stackSuffixFields (tm := tm) (space := space))

@[simp]
theorem program_wellFormedFields :
    (BoundedMachineAtom.wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        wellFormedFields (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.wellFormedFields, wellFormedFields]

end BoundedMachineProgram

end PeriodicCNF
end LeanTrominoes
