/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineProgramTemplates
import LeanTrominoes.PeriodicCNFMachineProgramStackTransform

/-!
# Affine templates for bounded-machine stack fields

The atom code of a fixed stack symbol is affine in its represented position.
This file instantiates the generic affine postorder language for stack-cell
tests, exact-one fields, equal shifted cells, and occupied-prefix constraints.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAffineProgram

open BoundedMachineAtom
open AffineProgramTemplates
open AffineTemplateEmitterMachine
open UnaryProgramTokens

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- Affine code of one fixed optional symbol at a shifted stack position. -/
def stackCellAtom (stack : tm.K) (symbol : Option (tm.Γ stack))
    (offset : Nat := 0) : Atom where
  base := Fintype.card (Option tm.Λ) +
    (Fintype.card tm.σ +
      (stackSymbolCode ⟨stack, symbol⟩ +
        BoundedMachineAtom.stackSymbolCount (tm := tm) * offset))
  stride := BoundedMachineAtom.stackSymbolCount (tm := tm)

@[simp]
theorem evaluate_stackCellAtom (stack : tm.K)
    (symbol : Option (tm.Γ stack)) (offset position : Nat) :
    (stackCellAtom (tm := tm) stack symbol offset).evaluate position =
      Fintype.card (Option tm.Λ) +
        (Fintype.card tm.σ +
          (stackSymbolCode ⟨stack, symbol⟩ +
            BoundedMachineAtom.stackSymbolCount (tm := tm) *
              (position + offset))) := by
  simp [stackCellAtom, Atom.evaluate]
  ring

/-- Affine codes for every value of one shifted stack cell. -/
def stackCellAtoms (stack : tm.K) (offset : Nat := 0) : List Atom :=
  (finiteValues (Option (tm.Γ stack))).map fun symbol =>
    stackCellAtom (tm := tm) stack symbol offset

@[simp]
theorem map_evaluate_stackCellAtoms (stack : tm.K)
    (offset position : Nat) :
    (stackCellAtoms (tm := tm) stack offset).map (Atom.evaluate position) =
      BoundedMachineProgram.stackCellAtoms (tm := tm) stack
        (position + offset) := by
  simp [stackCellAtoms, BoundedMachineProgram.stackCellAtoms,
    List.map_map, Function.comp_def]

def currentStackCellIs (stack : tm.K) (offset : Nat)
    (symbol : Option (tm.Γ stack)) : AffineProgramTemplates.Program :=
  AffineProgramTemplates.current
    (stackCellAtom (tm := tm) stack symbol offset)

def nextStackCellIs (stack : tm.K) (offset : Nat)
    (symbol : Option (tm.Γ stack)) : AffineProgramTemplates.Program :=
  AffineProgramTemplates.next
    (stackCellAtom (tm := tm) stack symbol offset)

@[simp]
theorem evaluate_currentStackCellIs (stack : tm.K) (offset position : Nat)
    (symbol : Option (tm.Γ stack)) :
    (currentStackCellIs (tm := tm) stack offset symbol).evaluate position =
      BoundedMachineProgram.currentStackCellIs (tm := tm) stack
        (position + offset) symbol := by
  simp [currentStackCellIs, BoundedMachineProgram.currentStackCellIs]

@[simp]
theorem evaluate_nextStackCellIs (stack : tm.K) (offset position : Nat)
    (symbol : Option (tm.Γ stack)) :
    (nextStackCellIs (tm := tm) stack offset symbol).evaluate position =
      BoundedMachineProgram.nextStackCellIs (tm := tm) stack
        (position + offset) symbol := by
  simp [nextStackCellIs, BoundedMachineProgram.nextStackCellIs]

/-- Exactly-one program for every possible value of one stack cell. -/
def stackCellExactlyOne (stack : tm.K) :
    AffineProgramTemplates.Program :=
  AffineProgramTemplates.currentExactlyOne
    (stackCellAtoms (tm := tm) stack)

@[simp]
theorem evaluate_stackCellExactlyOne (stack : tm.K) (position : Nat) :
    (stackCellExactlyOne (tm := tm) stack).evaluate position =
      BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
        position := by
  simp [stackCellExactlyOne,
    BoundedMachineProgram.stackCellExactlyOne]

/-- Equality between cells at independently shifted current and next
positions. -/
def stackCellsEqual (stack : tm.K) (currentOffset nextOffset : Nat) :
    AffineProgramTemplates.Program :=
  AffineProgramTemplates.vectorsEqual
    (stackCellAtoms (tm := tm) stack currentOffset)
    (stackCellAtoms (tm := tm) stack nextOffset)

@[simp]
theorem evaluate_stackCellsEqual (stack : tm.K)
    (currentOffset nextOffset position : Nat) :
    (stackCellsEqual (tm := tm) stack currentOffset nextOffset).evaluate
        position =
      BoundedMachineProgram.stackCellsEqual (tm := tm) stack
        (position + currentOffset) (position + nextOffset) := by
  simp [stackCellsEqual, BoundedMachineProgram.stackCellsEqual]

/-- Interior occupied-prefix constraint between positions `p` and `p + 1`.
The terminal position is the separate constant-true boundary case. -/
def stackSuffixInterior (stack : tm.K) :
    AffineProgramTemplates.Program :=
  AffineProgramTemplates.disjoin
    (AffineProgramTemplates.negate
      (currentStackCellIs (tm := tm) stack 0 none))
    (currentStackCellIs (tm := tm) stack 1 none)

@[simp]
theorem evaluate_stackSuffixInterior (stack : tm.K) (position : Nat) :
    (stackSuffixInterior (tm := tm) stack).evaluate position =
      TransitionProgram.disjoin
        (TransitionProgram.negate
          (TransitionProgram.current
            (BoundedMachineProgram.stackNoneAtom (tm := tm) stack position)))
        (TransitionProgram.current
          (BoundedMachineProgram.stackNoneAtom (tm := tm) stack
            (position + 1))) := by
  simp [stackSuffixInterior, BoundedMachineProgram.currentStackCellIs,
    BoundedMachineProgram.stackNoneAtom]

theorem evaluate_stackSuffixInterior_eq (stack : tm.K)
    {space position : Nat} (interior : position + 1 < space) :
    (stackSuffixInterior (tm := tm) stack).evaluate position =
      BoundedMachineProgram.stackSuffixExpression (tm := tm)
        (space := space) stack position := by
  rw [evaluate_stackSuffixInterior]
  simp [BoundedMachineProgram.stackSuffixExpression, interior]

theorem positionTokens_stackCellExactlyOne (stack : tm.K)
    (position : Nat) :
    positionTokens
        (AffineProgramTemplates.Program.recipes
          (stackCellExactlyOne (tm := tm) stack)) position =
      ofProgram
        (BoundedMachineProgram.stackCellExactlyOne (tm := tm) stack
          position) := by
  rw [AffineProgramTemplates.Program.positionTokens_recipes,
    evaluate_stackCellExactlyOne]

theorem positionTokens_stackCellsEqual (stack : tm.K)
    (currentOffset nextOffset position : Nat) :
    positionTokens
        (AffineProgramTemplates.Program.recipes
          (stackCellsEqual (tm := tm) stack currentOffset nextOffset))
        position =
      ofProgram
        (BoundedMachineProgram.stackCellsEqual (tm := tm) stack
          (position + currentOffset) (position + nextOffset)) := by
  rw [AffineProgramTemplates.Program.positionTokens_recipes,
    evaluate_stackCellsEqual]

theorem positionTokens_stackSuffixInterior (stack : tm.K)
    {space position : Nat} (interior : position + 1 < space) :
    positionTokens
        (AffineProgramTemplates.Program.recipes
          (stackSuffixInterior (tm := tm) stack)) position =
      ofProgram
        (BoundedMachineProgram.stackSuffixExpression (tm := tm)
          (space := space) stack position) := by
  rw [AffineProgramTemplates.Program.positionTokens_recipes,
    evaluate_stackSuffixInterior_eq stack interior]

end BoundedMachineAffineProgram
end PeriodicCNF
end LeanTrominoes
