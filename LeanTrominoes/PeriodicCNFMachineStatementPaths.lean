/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStackTransform

/-!
# Finite symbolic paths through TM2 statements

TM2 executes an entire `Stmt` atomically.  This file symbolically specializes
such a statement to a finite current control value.  Pushes and pops accumulate
as normalized stack transforms; a `peek` or `pop` branches only when it reads
one still-unknown source cell, over that stack's finite optional alphabet.
Every terminal path records its guard and complete next configuration.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- One terminal symbolic execution path through an atomic TM2 statement. -/
structure StatementPath (tm : FinTM2) (space clockBits : Nat) where
  guard : TransitionExpr
  label : Option tm.Λ
  control : tm.σ
  transforms : ∀ stack, StackTransform (tm.Γ stack)

/-- Add one observed source-cell condition to a symbolic path. -/
def StatementPath.andGuard
    (condition : TransitionExpr)
    (path : StatementPath tm space clockBits) :
    StatementPath tm space clockBits :=
  { path with guard := .and condition path.guard }

/-- Initially every stack is unchanged. -/
def identityStackTransforms : ∀ stack : tm.K,
    StackTransform (tm.Γ stack) :=
  fun stack => StackTransform.identity (tm.Γ stack)

/-- Symbolically execute an atomic statement from a concrete finite-control
value and accumulated normalized stack transforms. -/
def statementPaths :
    Turing.TM2.Stmt tm.Γ tm.Λ tm.σ →
      tm.σ →
      (∀ stack, StackTransform (tm.Γ stack)) →
      List (StatementPath tm space clockBits)
  | .push stackIndex write next, control, transforms =>
      statementPaths next control
        (Function.update transforms stackIndex
          ((transforms stackIndex).push (write control)))
  | .peek stackIndex read next, control, transforms =>
      match addedEq : (transforms stackIndex).added with
      | symbol :: _ =>
          statementPaths next (read control (some symbol)) transforms
      | [] =>
          if sourceExists : (transforms stackIndex).discard < space then
            (finiteValues (Option (tm.Γ stackIndex))).flatMap fun observed =>
              (statementPaths next (read control observed) transforms).map
                (StatementPath.andGuard
                  (currentStackCellIs (tm := tm) (clockBits := clockBits)
                    stackIndex
                    ⟨(transforms stackIndex).discard, sourceExists⟩ observed))
          else
            statementPaths next (read control none) transforms
  | .pop stackIndex read next, control, transforms =>
      let popped := Function.update transforms stackIndex
        (transforms stackIndex).pop
      match addedEq : (transforms stackIndex).added with
      | symbol :: _ =>
          statementPaths next (read control (some symbol)) popped
      | [] =>
          if sourceExists : (transforms stackIndex).discard < space then
            (finiteValues (Option (tm.Γ stackIndex))).flatMap fun observed =>
              (statementPaths next (read control observed) popped).map
                (StatementPath.andGuard
                  (currentStackCellIs (tm := tm) (clockBits := clockBits)
                    stackIndex
                    ⟨(transforms stackIndex).discard, sourceExists⟩ observed))
          else
            statementPaths next (read control none) popped
  | .load update next, control, transforms =>
      statementPaths next (update control) transforms
  | .branch test yes no, control, transforms =>
      if test control then
        statementPaths yes control transforms
      else
        statementPaths no control transforms
  | .goto target, control, transforms =>
      [{ guard := .constant true
         label := some (target control)
         control := control
         transforms := transforms }]
  | .halt, control, transforms =>
      [{ guard := .constant true
         label := none
         control := control
         transforms := transforms }]

/-- Require every stack to undergo the normalized transform stored by a
terminal symbolic path. -/
def StatementPath.stackExpression
    (path : StatementPath tm space clockBits) : TransitionExpr :=
  TransitionExpr.all ((finiteValues tm.K).map fun stack =>
    stackTransformExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack (path.transforms stack))

/-- Complete current/next expression for one terminal symbolic path. -/
def StatementPath.expression
    (path : StatementPath tm space clockBits) : TransitionExpr :=
  TransitionExpr.all
    [path.guard,
      nextLabelIs (tm := tm) (space := space)
        (clockBits := clockBits) path.label,
      nextControlIs (tm := tm) (space := space)
        (clockBits := clockBits) path.control,
      path.stackExpression]

/-- Disjunction of all terminal paths from one concrete current control. -/
def statementPathsExpression
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) : TransitionExpr :=
  TransitionExpr.any
    ((statementPaths (space := space) (clockBits := clockBits)
      statement control transforms).map StatementPath.expression)

/-- One atomic statement, including selection of its current control value. -/
def statementExpression
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : TransitionExpr :=
  TransitionExpr.any ((finiteValues tm.σ).map fun control =>
    .and
      (currentControlIs (tm := tm) (space := space)
        (clockBits := clockBits) control)
      (statementPathsExpression (tm := tm) (space := space)
        (clockBits := clockBits) statement control identityStackTransforms))

/-- One ordinary TM2 step, selected by the current live program label. -/
def machineStepExpression : TransitionExpr :=
  TransitionExpr.any ((finiteValues tm.Λ).map fun label =>
    .and
      (currentLabelIs (tm := tm) (space := space)
        (clockBits := clockBits) (some label))
      (statementExpression (tm := tm) (space := space)
        (clockBits := clockBits) (tm.m label)))

theorem TransitionExpr.any_atomsBelow
    {expressions : List TransitionExpr} {bound : Nat}
    (bounded : ∀ expression ∈ expressions,
      expression.AtomsBelow bound) :
    (TransitionExpr.any expressions).AtomsBelow bound := by
  induction expressions with
  | nil => trivial
  | cons expression expressions ih =>
      exact ⟨bounded expression (by simp),
        ih (fun member memberMem => bounded member (by simp [memberMem]))⟩

theorem StatementPath.stackExpression_atomsBelow
    (path : StatementPath tm space clockBits) :
    path.stackExpression.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackTransformExpression_atomsBelow stack (path.transforms stack)

theorem StatementPath.expression_atomsBelow
    (path : StatementPath tm space clockBits)
    (guardBelow : path.guard.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits))) :
    path.expression.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.all_atomsBelow
  intro expression expressionMem
  simp only [StatementPath.expression, List.mem_cons,
    List.not_mem_nil, or_false] at expressionMem
  rcases expressionMem with rfl | rfl | rfl | rfl
  · exact guardBelow
  · exact nextLabelIs_atomsBelow path.label
  · exact nextControlIs_atomsBelow path.control
  · exact path.stackExpression_atomsBelow

/-- Every generated symbolic guard mentions only allocated source atoms. -/
theorem statementPaths_guard_atomsBelow
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (path : StatementPath tm space clockBits)
    (pathMem : path ∈ statementPaths (space := space)
      (clockBits := clockBits) statement control transforms) :
    path.guard.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  induction statement generalizing control transforms path with
  | push stackIndex write next ih =>
      exact ih control
        (Function.update transforms stackIndex
          ((transforms stackIndex).push (write control))) path pathMem
  | peek stackIndex read next ih =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact ih _ _ _ pathMem
      · split at pathMem
        · rw [List.mem_flatMap] at pathMem
          obtain ⟨observed, _, pathMem⟩ := pathMem
          obtain ⟨sourcePath, sourceMem, rfl⟩ := List.mem_map.mp pathMem
          exact ⟨currentStackCellIs_atomsBelow stackIndex _ observed,
            ih _ _ _ sourceMem⟩
        · exact ih _ _ _ pathMem
  | pop stackIndex read next ih =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact ih _ _ _ pathMem
      · split at pathMem
        · rw [List.mem_flatMap] at pathMem
          obtain ⟨observed, _, pathMem⟩ := pathMem
          obtain ⟨sourcePath, sourceMem, rfl⟩ := List.mem_map.mp pathMem
          exact ⟨currentStackCellIs_atomsBelow stackIndex _ observed,
            ih _ _ _ sourceMem⟩
        · exact ih _ _ _ pathMem
  | load update next ih =>
      exact ih (update control) transforms path pathMem
  | branch test yes no yesIH noIH =>
      simp only [statementPaths] at pathMem
      split at pathMem
      · exact yesIH _ _ _ pathMem
      · exact noIH _ _ _ pathMem
  | goto target =>
      simp only [statementPaths, List.mem_singleton] at pathMem
      rcases pathMem with rfl
      trivial
  | halt =>
      simp only [statementPaths, List.mem_singleton] at pathMem
      rcases pathMem with rfl
      trivial

theorem statementPathsExpression_atomsBelow
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (statementPathsExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement control transforms).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.any_atomsBelow
  intro expression expressionMem
  obtain ⟨path, pathMem, rfl⟩ := List.mem_map.mp expressionMem
  exact path.expression_atomsBelow
    (statementPaths_guard_atomsBelow statement control transforms path pathMem)

theorem statementExpression_atomsBelow
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (statementExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.any_atomsBelow
  intro expression expressionMem
  obtain ⟨control, _, rfl⟩ := List.mem_map.mp expressionMem
  exact ⟨currentControlIs_atomsBelow control,
    statementPathsExpression_atomsBelow statement control _⟩

theorem machineStepExpression_atomsBelow :
    (machineStepExpression (tm := tm) (space := space)
      (clockBits := clockBits)).AtomsBelow
        (atomCount (tm := tm) (space := space) (clockBits := clockBits)) := by
  apply TransitionExpr.any_atomsBelow
  intro expression expressionMem
  obtain ⟨label, _, rfl⟩ := List.mem_map.mp expressionMem
  exact ⟨currentLabelIs_atomsBelow (some label),
    statementExpression_atomsBelow (tm.m label)⟩

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
