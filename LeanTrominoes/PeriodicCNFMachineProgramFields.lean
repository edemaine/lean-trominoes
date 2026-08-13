/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTransitionProgramVectors
import LeanTrominoes.PeriodicCNFMachineResetRelation

/-!
# Normalized postorder programs for bounded-machine fields

This file removes the first layer of semantic expression construction from
the periodic-CNF request printer.  Labels, controls, stack cells, complete
fixed configurations, and reset-clock vectors are expressed directly as flat
postorder instruction words.  Runtime-dependent atom names use the explicit
affine layout proved for `BoundedMachineAtom`.
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

/-- Fixed optional-label atom codes. -/
def labelAtoms : List Nat :=
  (finiteValues (Option tm.Λ)).map labelCode

/-- Affine finite-control atom codes. -/
def stateAtoms : List Nat :=
  (finiteValues tm.σ).map fun control =>
    Fintype.card (Option tm.Λ) + stateCode control

/-- Affine atom codes for every possible value of one stack cell. -/
def stackCellAtoms (stack : tm.K) (position : Nat) : List Nat :=
  (finiteValues (Option (tm.Γ stack))).map fun symbol =>
    Fintype.card (Option tm.Λ) +
      (Fintype.card tm.σ +
        (stackSymbolCode ⟨stack, symbol⟩ +
          BoundedMachineAtom.stackSymbolCount (tm := tm) * position))

/-- Affine little-endian reset-clock atom codes. -/
def clockAtoms : List Nat :=
  (List.finRange clockBits).map fun position =>
    Fintype.card (Option tm.Λ) +
      (Fintype.card tm.σ +
        (space * BoundedMachineAtom.stackSymbolCount (tm := tm) +
          position.val))

@[simp]
theorem labelAtoms_eq :
    labelAtoms (tm := tm) =
      BoundedMachineAtom.labelAtoms (tm := tm) (space := space)
        (clockBits := clockBits) := by
  exact BoundedMachineAtom.labelAtoms_eq_fixed_codes.symm

@[simp]
theorem stateAtoms_eq :
    stateAtoms (tm := tm) =
      BoundedMachineAtom.stateAtoms (tm := tm) (space := space)
        (clockBits := clockBits) := by
  exact BoundedMachineAtom.stateAtoms_eq_affine_codes.symm

@[simp]
theorem stackCellAtoms_eq (stack : tm.K) (position : Fin space) :
    stackCellAtoms (tm := tm) stack position.val =
      BoundedMachineAtom.stackCellAtoms (tm := tm)
        (clockBits := clockBits) stack position := by
  exact BoundedMachineAtom.stackCellAtoms_eq_affine_codes stack position |>.symm

@[simp]
theorem clockAtoms_eq :
    clockAtoms (tm := tm) (space := space) (clockBits := clockBits) =
      BoundedMachineAtom.clockAtoms (tm := tm) (space := space)
        (clockBits := clockBits) := by
  exact BoundedMachineAtom.clockAtoms_eq_affine_codes.symm

def currentLabelIs (label : Option tm.Λ) : TransitionProgram.Program :=
  TransitionProgram.current (labelCode label)

def nextLabelIs (label : Option tm.Λ) : TransitionProgram.Program :=
  TransitionProgram.next (labelCode label)

def currentControlIs (control : tm.σ) : TransitionProgram.Program :=
  TransitionProgram.current
    (Fintype.card (Option tm.Λ) + stateCode control)

def nextControlIs (control : tm.σ) : TransitionProgram.Program :=
  TransitionProgram.next
    (Fintype.card (Option tm.Λ) + stateCode control)

def currentStackCellIs (stack : tm.K) (position : Nat)
    (symbol : Option (tm.Γ stack)) : TransitionProgram.Program :=
  TransitionProgram.current
    (Fintype.card (Option tm.Λ) +
      (Fintype.card tm.σ +
        (stackSymbolCode ⟨stack, symbol⟩ +
          BoundedMachineAtom.stackSymbolCount (tm := tm) * position)))

def nextStackCellIs (stack : tm.K) (position : Nat)
    (symbol : Option (tm.Γ stack)) : TransitionProgram.Program :=
  TransitionProgram.next
    (Fintype.card (Option tm.Λ) +
      (Fintype.card tm.σ +
        (stackSymbolCode ⟨stack, symbol⟩ +
          BoundedMachineAtom.stackSymbolCount (tm := tm) * position)))

@[simp]
theorem program_currentLabelIs (label : Option tm.Λ) :
    (BoundedMachineAtom.currentLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).program = currentLabelIs label := by
  simp [BoundedMachineAtom.currentLabelIs, currentLabelIs,
    BoundedMachineAtom.code_label]

@[simp]
theorem program_nextLabelIs (label : Option tm.Λ) :
    (BoundedMachineAtom.nextLabelIs (tm := tm) (space := space)
      (clockBits := clockBits) label).program = nextLabelIs label := by
  simp [BoundedMachineAtom.nextLabelIs, nextLabelIs,
    BoundedMachineAtom.code_label]

@[simp]
theorem program_currentControlIs (control : tm.σ) :
    (BoundedMachineAtom.currentControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).program = currentControlIs control := by
  simp [BoundedMachineAtom.currentControlIs, currentControlIs,
    BoundedMachineAtom.code_state]

@[simp]
theorem program_nextControlIs (control : tm.σ) :
    (BoundedMachineAtom.nextControlIs (tm := tm) (space := space)
      (clockBits := clockBits) control).program = nextControlIs control := by
  simp [BoundedMachineAtom.nextControlIs, nextControlIs,
    BoundedMachineAtom.code_state]

@[simp]
theorem program_currentStackCellIs (stack : tm.K)
    (position : Fin space) (symbol : Option (tm.Γ stack)) :
    (BoundedMachineAtom.currentStackCellIs (tm := tm)
      (clockBits := clockBits) stack position symbol).program =
        currentStackCellIs stack position.val symbol := by
  simp [BoundedMachineAtom.currentStackCellIs, currentStackCellIs,
    BoundedMachineAtom.code_stack]

@[simp]
theorem program_nextStackCellIs (stack : tm.K)
    (position : Fin space) (symbol : Option (tm.Γ stack)) :
    (BoundedMachineAtom.nextStackCellIs (tm := tm)
      (clockBits := clockBits) stack position symbol).program =
        nextStackCellIs stack position.val symbol := by
  simp [BoundedMachineAtom.nextStackCellIs, nextStackCellIs,
    BoundedMachineAtom.code_stack]

def labelsEqual : TransitionProgram.Program :=
  TransitionProgram.vectorsEqual (labelAtoms (tm := tm))
    (labelAtoms (tm := tm))

def controlsEqual : TransitionProgram.Program :=
  TransitionProgram.vectorsEqual (stateAtoms (tm := tm))
    (stateAtoms (tm := tm))

def stackCellsEqual (stack : tm.K)
    (currentPosition nextPosition : Nat) : TransitionProgram.Program :=
  TransitionProgram.vectorsEqual
    (stackCellAtoms (tm := tm) stack currentPosition)
    (stackCellAtoms (tm := tm) stack nextPosition)

def stackEqual (stack : tm.K) : TransitionProgram.Program :=
  TransitionProgram.all ((List.finRange space).map fun position =>
    stackCellsEqual (tm := tm) stack position.val position.val)

def stacksEqual : TransitionProgram.Program :=
  TransitionProgram.all ((finiteValues tm.K).map fun stack =>
    stackEqual (tm := tm) (space := space) stack)

@[simp]
theorem program_labelsEqual :
    (BoundedMachineAtom.labelsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).program = labelsEqual (tm := tm) := by
  simp only [BoundedMachineAtom.labelsEqual,
    TransitionExpr.program_vectorsEqual, labelsEqual]
  rw [← labelAtoms_eq (tm := tm) (space := space)
    (clockBits := clockBits)]

@[simp]
theorem program_controlsEqual :
    (BoundedMachineAtom.controlsEqual (tm := tm) (space := space)
      (clockBits := clockBits)).program = controlsEqual (tm := tm) := by
  simp only [BoundedMachineAtom.controlsEqual,
    TransitionExpr.program_vectorsEqual, controlsEqual]
  rw [← stateAtoms_eq (tm := tm) (space := space)
    (clockBits := clockBits)]

@[simp]
theorem program_stackCellsEqual (stack : tm.K)
    (currentPosition nextPosition : Fin space) :
    (BoundedMachineAtom.stackCellsEqual (tm := tm)
      (clockBits := clockBits) stack currentPosition nextPosition).program =
        stackCellsEqual (tm := tm) stack currentPosition.val
          nextPosition.val := by
  simp only [BoundedMachineAtom.stackCellsEqual,
    TransitionExpr.program_vectorsEqual, stackCellsEqual]
  rw [← stackCellAtoms_eq (tm := tm) (clockBits := clockBits) stack
      currentPosition,
    ← stackCellAtoms_eq (tm := tm) (clockBits := clockBits) stack
      nextPosition]

@[simp]
theorem program_stackEqual (stack : tm.K) :
    (BoundedMachineAtom.stackEqual (tm := tm) (space := space)
      (clockBits := clockBits) stack).program =
        stackEqual (tm := tm) (space := space) stack := by
  simp [BoundedMachineAtom.stackEqual, stackEqual, List.map_map,
    Function.comp_def]

@[simp]
theorem program_stacksEqual :
    (BoundedMachineAtom.stacksEqual (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        stacksEqual (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.stacksEqual, stacksEqual, List.map_map,
    Function.comp_def]

/-- Test one fixed current stack over every represented position. -/
def currentStackIs (target : tm.Cfg) (stack : tm.K) :
    TransitionProgram.Program :=
  TransitionProgram.all ((List.finRange space).map fun position =>
    currentStackCellIs (tm := tm) stack position.val
      (target.stk stack)[position.val]?)

/-- Test one complete fixed current configuration. -/
def currentConfigIs (target : tm.Cfg) : TransitionProgram.Program :=
  TransitionProgram.conjoin (currentLabelIs (tm := tm) target.l)
    (TransitionProgram.conjoin (currentControlIs (tm := tm) target.var)
      (TransitionProgram.all ((finiteValues tm.K).map fun stack =>
        currentStackIs (tm := tm) (space := space) target stack)))

/-- Test one fixed next stack over every represented position. -/
def nextStackIs (target : tm.Cfg) (stack : tm.K) :
    TransitionProgram.Program :=
  TransitionProgram.all ((List.finRange space).map fun position =>
    nextStackCellIs (tm := tm) stack position.val
      (target.stk stack)[position.val]?)

/-- Test one complete fixed next configuration. -/
def nextConfigIs (target : tm.Cfg) : TransitionProgram.Program :=
  TransitionProgram.conjoin (nextLabelIs (tm := tm) target.l)
    (TransitionProgram.conjoin (nextControlIs (tm := tm) target.var)
      (TransitionProgram.all ((finiteValues tm.K).map fun stack =>
        nextStackIs (tm := tm) (space := space) target stack)))

@[simp]
theorem program_currentStackIs (target : tm.Cfg) (stack : tm.K) :
    (BoundedMachineAtom.currentStackIs (tm := tm) (space := space)
      (clockBits := clockBits) target stack).program =
        currentStackIs (tm := tm) (space := space) target stack := by
  simp [BoundedMachineAtom.currentStackIs, currentStackIs, List.map_map,
    Function.comp_def]

@[simp]
theorem program_currentConfigIs (target : tm.Cfg) :
    (BoundedMachineAtom.currentConfigIs (tm := tm) (space := space)
      (clockBits := clockBits) target).program =
        currentConfigIs (tm := tm) (space := space) target := by
  simp [BoundedMachineAtom.currentConfigIs, currentConfigIs, List.map_map,
    Function.comp_def]

@[simp]
theorem program_nextStackIs (target : tm.Cfg) (stack : tm.K) :
    (BoundedMachineAtom.nextStackIs (tm := tm) (space := space)
      (clockBits := clockBits) target stack).program =
        nextStackIs (tm := tm) (space := space) target stack := by
  simp [BoundedMachineAtom.nextStackIs, nextStackIs, List.map_map,
    Function.comp_def]

@[simp]
theorem program_nextConfigIs (target : tm.Cfg) :
    (BoundedMachineAtom.nextConfigIs (tm := tm) (space := space)
      (clockBits := clockBits) target).program =
        nextConfigIs (tm := tm) (space := space) target := by
  simp [BoundedMachineAtom.nextConfigIs, nextConfigIs, List.map_map,
    Function.comp_def]

/-- No-overflow reset-clock successor program. -/
def clockSuccessor : TransitionProgram.Program :=
  TransitionProgram.binarySuccessor
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))

/-- Program forcing every next reset-clock bit to zero. -/
def clockReset : TransitionProgram.Program :=
  TransitionProgram.all
    ((clockAtoms (tm := tm) (space := space)
      (clockBits := clockBits)).map fun atom =>
    TransitionProgram.negate (TransitionProgram.next atom))

@[simp]
theorem program_clockSuccessor :
    (BoundedMachineAtom.clockSuccessor (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        clockSuccessor (tm := tm) (space := space)
          (clockBits := clockBits) := by
  simp [BoundedMachineAtom.clockSuccessor, clockSuccessor]

@[simp]
theorem program_clockReset :
    (BoundedMachineAtom.clockReset (tm := tm) (space := space)
      (clockBits := clockBits)).program =
        clockReset (tm := tm) (space := space) (clockBits := clockBits) := by
  simp [BoundedMachineAtom.clockReset, clockReset, List.map_map,
    Function.comp_def]

end BoundedMachineProgram

end PeriodicCNF
end LeanTrominoes
