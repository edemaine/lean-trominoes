/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStepSize

/-!
# Affine form of the bounded TM2 step budget

The explicit size budget for a fixed finite machine is affine in represented
stack width.  This file exposes its slope and intercept, ready for composition
with a source decider's polynomial space certificate.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

private theorem sum_affine {Value : Type*} (values : List Value)
    (slope intercept : Value → Nat) (width : Nat) :
    (values.map fun value => slope value * width + intercept value).sum =
      (values.map slope).sum * width + (values.map intercept).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Slope of the all-stack transform budget. -/
def stackTransformFamilySlope : Nat :=
  Fintype.card tm.K * (stackTransformCellNodeBudget (tm := tm) + 1)

/-- Intercept of the all-stack transform budget. -/
def stackTransformFamilyIntercept : Nat :=
  Fintype.card tm.K * 4 + 1

theorem stackTransformFamilyNodeBudget_eq_affine :
    stackTransformFamilyNodeBudget (tm := tm) (space := space) =
      stackTransformFamilySlope (tm := tm) * space +
        stackTransformFamilyIntercept (tm := tm) := by
  unfold stackTransformFamilyNodeBudget stackTransformFamilySlope
    stackTransformFamilyIntercept
  ring

/-- Intercept of one terminal-path budget for a fixed statement. -/
def statementPathIntercept
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  2 * statementObservationDepth statement + 1 +
    stackTransformFamilyIntercept (tm := tm) + 7

theorem statementPathNodeBudget_eq_affine
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    statementPathNodeBudget (tm := tm) (space := space) statement =
      stackTransformFamilySlope (tm := tm) * space +
        statementPathIntercept (tm := tm) statement := by
  unfold statementPathNodeBudget statementPathIntercept
  rw [stackTransformFamilyNodeBudget_eq_affine]
  ring

/-- Slope after disjoining all terminal paths of one statement. -/
def statementPathsSlope
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  statementPathCountBudget statement * stackTransformFamilySlope (tm := tm)

/-- Intercept after disjoining all terminal paths of one statement. -/
def statementPathsIntercept
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  statementPathCountBudget statement *
      (statementPathIntercept (tm := tm) statement + 1) + 1

theorem statementPathsNodeBudget_eq_affine
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    statementPathsNodeBudget (tm := tm) (space := space) statement =
      statementPathsSlope (tm := tm) statement * space +
        statementPathsIntercept (tm := tm) statement := by
  unfold statementPathsNodeBudget statementPathsSlope statementPathsIntercept
  rw [statementPathNodeBudget_eq_affine]
  ring

/-- Slope after enumerating all finite-control values for one statement. -/
def statementSlope
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  Fintype.card tm.σ * statementPathsSlope (tm := tm) statement

/-- Intercept after enumerating all finite-control values for one statement. -/
def statementIntercept
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  Fintype.card tm.σ *
      (statementPathsIntercept (tm := tm) statement + 3) + 1

theorem statementNodeBudget_eq_affine
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    statementNodeBudget (tm := tm) (space := space) statement =
      statementSlope (tm := tm) statement * space +
        statementIntercept (tm := tm) statement := by
  unfold statementNodeBudget statementSlope statementIntercept
  rw [statementPathsNodeBudget_eq_affine]
  ring

/-- Slope of the complete ordinary-step expression for the fixed machine. -/
def machineStepSlope : Nat :=
  ((finiteValues tm.Λ).map fun label =>
    statementSlope (tm := tm) (tm.m label)).sum

/-- Intercept of the complete ordinary-step expression for the fixed machine. -/
def machineStepIntercept : Nat :=
  ((finiteValues tm.Λ).map fun label =>
    statementIntercept (tm := tm) (tm.m label) + 2).sum +
      Fintype.card tm.Λ + 1

/-- The complete ordinary-step node budget is exactly affine in represented
stack width. -/
theorem machineStepNodeBudget_eq_affine :
    machineStepNodeBudget (tm := tm) (space := space) =
      machineStepSlope (tm := tm) * space +
        machineStepIntercept (tm := tm) := by
  unfold machineStepNodeBudget
  simp_rw [statementNodeBudget_eq_affine]
  simp_rw [Nat.add_assoc]
  rw [sum_affine (finiteValues tm.Λ)
    (fun label => statementSlope (tm := tm) (tm.m label))
    (fun label => statementIntercept (tm := tm) (tm.m label) + 2) space]
  unfold machineStepSlope machineStepIntercept
  ring

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
