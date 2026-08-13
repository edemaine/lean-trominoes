/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineProgramStackTransform

/-!
# Program-valued symbolic paths through finite TM2 statements

`BoundedMachineAtom.statementPaths` builds semantic transition expressions.
The request printer instead needs a finite-control traversal that directly
produces postorder instruction words.  This file mirrors the symbolic
executor with program-valued guards, proves an exact path-by-path relation to
the semantic executor, and assembles the complete ordinary-step postorder
program without constructing a `TransitionExpr`.
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

/-- One terminal symbolic statement path whose guard is already a postorder
instruction word. -/
structure StatementProgramPath (tm : FinTM2) where
  guard : TransitionProgram.Program
  label : Option tm.Λ
  control : tm.σ
  transforms : ∀ stack, StackTransform (tm.Γ stack)

namespace StatementProgramPath

def andGuard (condition : TransitionProgram.Program)
    (path : StatementProgramPath tm) : StatementProgramPath tm :=
  { path with guard := TransitionProgram.conjoin condition path.guard }

/-- Forget only the semantic expression wrapper around an existing symbolic
path guard. -/
def ofExpression
    (path : BoundedMachineAtom.StatementPath tm space clockBits) :
    StatementProgramPath tm where
  guard := path.guard.program
  label := path.label
  control := path.control
  transforms := path.transforms

@[simp]
theorem ofExpression_andGuard (condition : TransitionExpr)
    (path : BoundedMachineAtom.StatementPath tm space clockBits) :
    ofExpression (path.andGuard condition) =
      (ofExpression path).andGuard condition.program := by
  cases path
  rfl

@[simp]
theorem map_ofExpression_map_andGuard (condition : TransitionExpr)
    (paths : List (BoundedMachineAtom.StatementPath tm space clockBits)) :
    (paths.map (BoundedMachineAtom.StatementPath.andGuard condition)).map
        ofExpression =
      (paths.map ofExpression).map
        (StatementProgramPath.andGuard condition.program) := by
  simp [List.map_map, Function.comp_def]

end StatementProgramPath

/-- Symbolically execute one atomic statement while retaining guards directly
as flat postorder programs. -/
def statementProgramPaths :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      tm.σ →
      (∀ stack, StackTransform (tm.Γ stack)) →
      List (StatementProgramPath tm)
  | .push stackIndex write next, control, transforms =>
      statementProgramPaths next control
        (Function.update transforms stackIndex
          ((transforms stackIndex).push (write control)))
  | .peek stackIndex read next, control, transforms =>
      match (transforms stackIndex).added with
      | symbol :: _ =>
          statementProgramPaths next (read control (some symbol)) transforms
      | [] =>
          if (transforms stackIndex).discard < space then
            (finiteValues (Option (tm.Γ stackIndex))).flatMap fun observed =>
              (statementProgramPaths next (read control observed)
                transforms).map
                (StatementProgramPath.andGuard
                  (currentStackCellIs (tm := tm) stackIndex
                    (transforms stackIndex).discard observed))
          else
            statementProgramPaths next (read control none) transforms
  | .pop stackIndex read next, control, transforms =>
      let popped := Function.update transforms stackIndex
        (transforms stackIndex).pop
      match (transforms stackIndex).added with
      | symbol :: _ =>
          statementProgramPaths next (read control (some symbol)) popped
      | [] =>
          if (transforms stackIndex).discard < space then
            (finiteValues (Option (tm.Γ stackIndex))).flatMap fun observed =>
              (statementProgramPaths next (read control observed) popped).map
                (StatementProgramPath.andGuard
                  (currentStackCellIs (tm := tm) stackIndex
                    (transforms stackIndex).discard observed))
          else
            statementProgramPaths next (read control none) popped
  | .load update next, control, transforms =>
      statementProgramPaths next (update control) transforms
  | .branch test yes no, control, transforms =>
      if test control then
        statementProgramPaths yes control transforms
      else
        statementProgramPaths no control transforms
  | .goto target, control, transforms =>
      [{ guard := TransitionProgram.constant true
         label := some (target control)
         control := control
         transforms := transforms }]
  | .halt, control, transforms =>
      [{ guard := TransitionProgram.constant true
         label := none
         control := control
         transforms := transforms }]

@[simp]
theorem map_ofExpression_statementPaths
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (BoundedMachineAtom.statementPaths (space := space)
      (clockBits := clockBits) statement control transforms).map
        StatementProgramPath.ofExpression =
      statementProgramPaths (tm := tm) (space := space)
        statement control transforms := by
  induction statement generalizing control transforms with
  | push stackIndex write next induction =>
      exact induction _ _
  | peek stackIndex read next induction =>
      simp only [BoundedMachineAtom.statementPaths, statementProgramPaths]
      cases addedEq : (transforms stackIndex).added with
      | cons symbol tail =>
          simp only [addedEq]
          exact induction _ _
      | nil =>
        simp only [addedEq]
        by_cases sourceExists : (transforms stackIndex).discard < space
        · simp only [sourceExists, dif_pos, if_pos]
          rw [List.map_flatMap]
          apply List.flatMap_congr
          intro observed _
          rw [StatementProgramPath.map_ofExpression_map_andGuard,
            induction]
          simp
        · simp only [sourceExists, dif_neg, if_neg]
          exact induction _ _
  | pop stackIndex read next induction =>
      simp only [BoundedMachineAtom.statementPaths, statementProgramPaths]
      cases addedEq : (transforms stackIndex).added with
      | cons symbol tail =>
          simp only [addedEq]
          exact induction _ _
      | nil =>
        simp only [addedEq]
        by_cases sourceExists : (transforms stackIndex).discard < space
        · simp only [sourceExists, dif_pos, if_pos]
          rw [List.map_flatMap]
          apply List.flatMap_congr
          intro observed _
          rw [StatementProgramPath.map_ofExpression_map_andGuard,
            induction]
          simp
        · simp only [sourceExists, dif_neg, if_neg]
          exact induction _ _
  | load update next induction =>
      exact induction _ _
  | branch test yes no yesIH noIH =>
      simp only [BoundedMachineAtom.statementPaths, statementProgramPaths]
      split
      · exact yesIH _ _
      · exact noIH _ _
  | goto target => rfl
  | halt => rfl

namespace StatementProgramPath

def stackProgram (path : StatementProgramPath tm) :
    TransitionProgram.Program :=
  TransitionProgram.all ((finiteValues tm.K).map fun stack =>
    stackTransform (tm := tm) (space := space) stack
      (path.transforms stack))

def program (path : StatementProgramPath tm) :
    TransitionProgram.Program :=
  TransitionProgram.all
    [path.guard,
      nextLabelIs (tm := tm) path.label,
      nextControlIs (tm := tm) path.control,
      path.stackProgram (tm := tm) (space := space)]

@[simp]
theorem program_stackExpression
    (path : BoundedMachineAtom.StatementPath tm space clockBits) :
    path.stackExpression.program =
      (ofExpression path).stackProgram (tm := tm) (space := space) := by
  cases path
  simp [BoundedMachineAtom.StatementPath.stackExpression, stackProgram,
    StatementProgramPath.ofExpression, List.map_map, Function.comp_def]

@[simp]
theorem program_expression
    (path : BoundedMachineAtom.StatementPath tm space clockBits) :
    path.expression.program =
      (ofExpression path).program (tm := tm) (space := space) := by
  cases path
  simp [BoundedMachineAtom.StatementPath.expression, program,
    StatementProgramPath.ofExpression]

end StatementProgramPath

def statementPathsProgram
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    TransitionProgram.Program :=
  TransitionProgram.any
    ((statementProgramPaths (tm := tm) (space := space)
      statement control transforms).map fun path =>
        path.program (tm := tm) (space := space))

def statementProgram
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    TransitionProgram.Program :=
  TransitionProgram.any ((finiteValues tm.σ).map fun control =>
    TransitionProgram.conjoin
      (currentControlIs (tm := tm) control)
      (statementPathsProgram (tm := tm) (space := space) statement control
        BoundedMachineAtom.identityStackTransforms))

def machineStep : TransitionProgram.Program :=
  TransitionProgram.any ((finiteValues tm.Λ).map fun label =>
    TransitionProgram.conjoin
      (currentLabelIs (tm := tm) (some label))
      (statementProgram (tm := tm) (space := space) (tm.m label)))

@[simp]
theorem program_statementPathsExpression
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (BoundedMachineAtom.statementPathsExpression (tm := tm)
      (space := space) (clockBits := clockBits) statement control
      transforms).program =
        statementPathsProgram (tm := tm) (space := space)
          statement control transforms := by
  rw [BoundedMachineAtom.statementPathsExpression,
    TransitionExpr.program_any]
  unfold statementPathsProgram
  rw [← map_ofExpression_statementPaths (tm := tm) (space := space)
    (clockBits := clockBits)]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro path _
  exact StatementProgramPath.program_expression path

@[simp]
theorem program_statementExpression
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (BoundedMachineAtom.statementExpression (tm := tm)
      (space := space) (clockBits := clockBits) statement).program =
        statementProgram (tm := tm) (space := space) statement := by
  simp [BoundedMachineAtom.statementExpression, statementProgram,
    List.map_map, Function.comp_def]

@[simp]
theorem program_machineStepExpression :
    (BoundedMachineAtom.machineStepExpression (tm := tm)
      (space := space) (clockBits := clockBits)).program =
        machineStep (tm := tm) (space := space) := by
  simp [BoundedMachineAtom.machineStepExpression, machineStep,
    List.map_map, Function.comp_def]

end BoundedMachineProgram

end PeriodicCNF
end LeanTrominoes
