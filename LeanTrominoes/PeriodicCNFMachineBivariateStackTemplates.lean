/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMarkedBivariateEmitterPipeline
import LeanTrominoes.PeriodicCNFBivariateProgramTokenAlgebra
import LeanTrominoes.PeriodicCNFMachineProgramStackTransform
import LeanTrominoes.PeriodicCNFMachineOneHotEmitterSpec

/-!
# Bivariate templates for end-relative bounded-stack fields

Instantiate the bivariate program language with stack-cell atom codes at
`fixedOffset + firstCount + intervalPosition`.  The resulting templates cover
both individual current/next cell tests and complete optional-cell equality.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineBivariateStack

open BivariateProgramTemplates
open BivariateProgramTokenAlgebra
open UnaryProgramTokens
open BoundedMachineAtom

variable {tm : FinTM2}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- One optional stack-symbol atom at an offset followed by the two runtime
counters. -/
def stackCellAtom (stack : tm.K) (symbol : Option (tm.Γ stack))
    (fixedOffset : Nat := 0) : BivariateProgramTemplates.Atom where
  base := Fintype.card (Option tm.Λ) +
    (Fintype.card tm.σ +
      (BoundedMachineAtom.stackSymbolCode ⟨stack, symbol⟩ +
        BoundedMachineAtom.stackSymbolCount (tm := tm) * fixedOffset))
  firstStride := BoundedMachineAtom.stackSymbolCount (tm := tm)
  secondStride := BoundedMachineAtom.stackSymbolCount (tm := tm)

@[simp]
theorem evaluate_stackCellAtom (stack : tm.K)
    (symbol : Option (tm.Γ stack))
    (fixedOffset first position : Nat) :
    (stackCellAtom (tm := tm) stack symbol fixedOffset).evaluate
        first position =
      Fintype.card (Option tm.Λ) +
        (Fintype.card tm.σ +
          (BoundedMachineAtom.stackSymbolCode ⟨stack, symbol⟩ +
            BoundedMachineAtom.stackSymbolCount (tm := tm) *
              (fixedOffset + first + position))) := by
  simp [stackCellAtom, BivariateProgramTemplates.Atom.evaluate]
  ring

def stackCellAtoms (stack : tm.K) (fixedOffset : Nat := 0) :
    List BivariateProgramTemplates.Atom :=
  (finiteValues (Option (tm.Γ stack))).map fun symbol =>
    stackCellAtom (tm := tm) stack symbol fixedOffset

@[simp]
theorem map_evaluate_stackCellAtoms (stack : tm.K)
    (fixedOffset first position : Nat) :
    (stackCellAtoms (tm := tm) stack fixedOffset).map
        (BivariateProgramTemplates.Atom.evaluate first position) =
      BoundedMachineProgram.stackCellAtoms (tm := tm) stack
        (fixedOffset + first + position) := by
  simp [stackCellAtoms, BoundedMachineProgram.stackCellAtoms,
    List.map_map, Function.comp_def]

def currentStackCellIs (stack : tm.K) (fixedOffset : Nat)
    (symbol : Option (tm.Γ stack)) : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.current
    (stackCellAtom (tm := tm) stack symbol fixedOffset)

def nextStackCellIs (stack : tm.K) (fixedOffset : Nat)
    (symbol : Option (tm.Γ stack)) : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.next
    (stackCellAtom (tm := tm) stack symbol fixedOffset)

@[simp]
theorem evaluate_currentStackCellIs (stack : tm.K)
    (fixedOffset first position : Nat)
    (symbol : Option (tm.Γ stack)) :
    (currentStackCellIs (tm := tm) stack fixedOffset symbol).evaluate
        first position =
      BoundedMachineProgram.currentStackCellIs (tm := tm) stack
        (fixedOffset + first + position) symbol := by
  simp [currentStackCellIs, BoundedMachineProgram.currentStackCellIs]

@[simp]
theorem evaluate_nextStackCellIs (stack : tm.K)
    (fixedOffset first position : Nat)
    (symbol : Option (tm.Γ stack)) :
    (nextStackCellIs (tm := tm) stack fixedOffset symbol).evaluate
        first position =
      BoundedMachineProgram.nextStackCellIs (tm := tm) stack
        (fixedOffset + first + position) symbol := by
  simp [nextStackCellIs, BoundedMachineProgram.nextStackCellIs]

/-- Equality between current and next optional-cell vectors at independently
offset positions following the same two counters. -/
def stackCellsEqual (stack : tm.K)
    (currentOffset nextOffset : Nat) : BivariateProgramTemplates.Program :=
  BivariateProgramTemplates.vectorsEqual
    (stackCellAtoms (tm := tm) stack currentOffset)
    (stackCellAtoms (tm := tm) stack nextOffset)

@[simp]
theorem evaluate_stackCellsEqual (stack : tm.K)
    (currentOffset nextOffset first position : Nat) :
    (stackCellsEqual (tm := tm) stack currentOffset nextOffset).evaluate
        first position =
      BoundedMachineProgram.stackCellsEqual (tm := tm) stack
        (currentOffset + first + position)
        (nextOffset + first + position) := by
  simp [stackCellsEqual, BoundedMachineProgram.stackCellsEqual]

theorem positionRangeTokens_nextStackCellIs (stack : tm.K)
    (fixedOffset first count : Nat) (symbol : Option (tm.Γ stack)) :
    BivariateTemplateEmitterMachine.positionRangeTokens
        (nextStackCellIs (tm := tm) stack fixedOffset symbol).recipes
        first 0 count =
      (List.range count).flatMap fun position =>
        ofProgram
          (BoundedMachineProgram.nextStackCellIs (tm := tm) stack
            (fixedOffset + first + position) symbol) := by
  rw [BivariateProgramTokenAlgebra.positionRangeTokens_program,
    BoundedMachineOneHotEmitter.positions_zero_eq_range]
  apply List.flatMap_congr
  intro position _
  rw [evaluate_nextStackCellIs]

theorem positionRangeTokens_stackCellsEqual (stack : tm.K)
    (currentOffset nextOffset first count : Nat) :
    BivariateTemplateEmitterMachine.positionRangeTokens
        (stackCellsEqual (tm := tm) stack currentOffset nextOffset).recipes
        first 0 count =
      (List.range count).flatMap fun position =>
        ofProgram
          (BoundedMachineProgram.stackCellsEqual (tm := tm) stack
            (currentOffset + first + position)
            (nextOffset + first + position)) := by
  rw [BivariateProgramTokenAlgebra.positionRangeTokens_program,
    BoundedMachineOneHotEmitter.positions_zero_eq_range]
  apply List.flatMap_congr
  intro position _
  rw [evaluate_stackCellsEqual]

end BoundedMachineBivariateStack
end PeriodicCNF
end LeanTrominoes
