/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramWellFormed

/-!
# Normalized postorder programs for bounded stack transforms

Atomic TM2 statements normalize their stack effects to a fixed pushed prefix
and a fixed source discard.  This file mirrors the corresponding bounded
cell, fit, and whole-stack expressions directly as instruction words.  The
only runtime loop is the explicit represented stack width.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineProgram

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def stackTransformCell (stack : tm.K)
    (transform : StackTransform (tm.Γ stack))
    (position : Fin space) : TransitionProgram.Program :=
  if addedPosition : position.val < transform.added.length then
    nextStackCellIs (tm := tm) stack position.val
      (some transform.added[position.val])
  else
    let source := position.val - transform.added.length + transform.discard
    if sourcePosition : source < space then
      stackCellsEqual (tm := tm) stack source position.val
    else
      nextStackCellIs (tm := tm) stack position.val none

def stackTransformFits (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    TransitionProgram.Program :=
  if _addedFits : transform.added.length ≤ space then
    if transform.firstOmitted space < space then
      currentStackCellIs (tm := tm) stack
        (transform.firstOmitted space) none
    else
      TransitionProgram.constant true
  else
    TransitionProgram.constant false

def stackTransform (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    TransitionProgram.Program :=
  TransitionProgram.conjoin
    (stackTransformFits (tm := tm) (space := space) stack transform)
    (TransitionProgram.all ((List.finRange space).map fun position =>
      stackTransformCell (tm := tm) stack transform position))

@[simp]
theorem program_stackTransformCell (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) (position : Fin space) :
    (BoundedMachineAtom.stackTransformCellExpression (tm := tm)
      (clockBits := clockBits) stack transform position).program =
        stackTransformCell (tm := tm) stack transform position := by
  unfold BoundedMachineAtom.stackTransformCellExpression stackTransformCell
  by_cases addedPosition : position.val < transform.added.length
  · simp [addedPosition]
  · simp only [addedPosition]
    by_cases sourcePosition :
        position.val - transform.added.length + transform.discard < space
    · simp [sourcePosition]
    · simp [sourcePosition]

@[simp]
theorem program_stackTransformFits (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    (BoundedMachineAtom.stackTransformFitsExpression (tm := tm)
      (space := space) (clockBits := clockBits) stack transform).program =
        stackTransformFits (tm := tm) (space := space) stack transform := by
  unfold BoundedMachineAtom.stackTransformFitsExpression stackTransformFits
  by_cases addedFits : transform.added.length ≤ space
  · simp only [addedFits, dif_pos]
    by_cases omittedExists : transform.firstOmitted space < space
    · simp [omittedExists]
    · simp [omittedExists]
  · simp [addedFits]

@[simp]
theorem program_stackTransform (stack : tm.K)
    (transform : StackTransform (tm.Γ stack)) :
    (BoundedMachineAtom.stackTransformExpression (tm := tm)
      (space := space) (clockBits := clockBits) stack transform).program =
        stackTransform (tm := tm) (space := space) stack transform := by
  simp [BoundedMachineAtom.stackTransformExpression, stackTransform,
    List.map_map, Function.comp_def]

end BoundedMachineProgram

end PeriodicCNF
end LeanTrominoes
