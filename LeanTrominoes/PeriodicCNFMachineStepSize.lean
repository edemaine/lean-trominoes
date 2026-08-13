/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineStatementSize

/-!
# Size of the bounded TM2 step expression

This file combines the fixed symbolic-path budgets with the linear expression
for normalized stack transforms.  It produces an explicit affine-in-width
bound for the complete ordinary-step expression of a fixed finite TM2 machine.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

private theorem sum_le_length_mul (values : List Nat) (bound : Nat)
    (bounded : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      calc
        value + values.sum ≤ bound + values.length * bound :=
          Nat.add_le_add (bounded value (by simp))
            (ih (fun member memberMem => bounded member (by simp [memberMem])))
        _ = (values.length + 1) * bound := by ring

private theorem sum_map_le {Value : Type*} (values : List Value)
    (first second : Value → Nat)
    (bounded : ∀ value ∈ values, first value ≤ second value) :
    (values.map first).sum ≤ (values.map second).sum := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (bounded value (by simp))
        (ih (fun member memberMem => bounded member (by simp [memberMem])))

/-- Uniform machine-dependent budget for one transformed stack cell. -/
def stackTransformCellNodeBudget : Nat :=
  10 * fieldCardBudget (tm := tm) + 1

private theorem stack_card_le_fieldCardBudget (stack : tm.K) :
    Fintype.card (Option (tm.Γ stack)) ≤ fieldCardBudget (tm := tm) := by
  classical
  have stackRate :
      Fintype.card (Option (tm.Γ stack)) ≤ stackCellBitRate (tm := tm) := by
    unfold stackCellBitRate
    exact Finset.single_le_sum
      (f := fun candidate : tm.K => Fintype.card (Option (tm.Γ candidate)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ stack)
  unfold fieldCardBudget
  omega

/-- Every output-cell transform has constant size for a fixed machine. -/
theorem stackTransformCellExpression_gateCount_le
    (stack : tm.K) (transform : StackTransform (tm.Γ stack))
    (position : Fin space) :
    (stackTransformCellExpression (tm := tm) (clockBits := clockBits)
      stack transform position).gateCount ≤
      stackTransformCellNodeBudget (tm := tm) := by
  unfold stackTransformCellExpression
  split
  · unfold stackTransformCellNodeBudget
    change 1 ≤ 10 * fieldCardBudget (tm := tm) + 1
    omega
  · dsimp only
    split
    · unfold stackCellsEqual
      rw [TransitionExpr.vectorsEqual_gateCount_of_length_eq]
      · rw [stackCellAtoms_length]
        unfold stackTransformCellNodeBudget
        have cardBound := stack_card_le_fieldCardBudget (tm := tm) stack
        omega
      · simp only [stackCellAtoms_length]
    · unfold stackTransformCellNodeBudget
      change 1 ≤ 10 * fieldCardBudget (tm := tm) + 1
      omega

@[simp]
theorem stackTransformFitsExpression_gateCount
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    (stackTransformFitsExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).gateCount = 1 := by
  unfold stackTransformFitsExpression
  split
  · split <;> rfl
  · rfl

/-- One normalized stack-transform expression is affine in stack width. -/
theorem stackTransformExpression_gateCount_le
    (stack : tm.K) (transform : StackTransform (tm.Γ stack)) :
    (stackTransformExpression (tm := tm) (space := space)
      (clockBits := clockBits) stack transform).gateCount ≤
      space * (stackTransformCellNodeBudget (tm := tm) + 1) + 3 := by
  rw [stackTransformExpression, TransitionExpr.gateCount,
    stackTransformFitsExpression_gateCount, TransitionExpr.all_gateCount]
  have cellsBound :
      (((List.finRange space).map fun position =>
        stackTransformCellExpression (tm := tm) (clockBits := clockBits)
          stack transform position).map TransitionExpr.gateCount).sum ≤
        space * stackTransformCellNodeBudget (tm := tm) := by
    simpa only [List.length_map, List.length_finRange] using
      (sum_le_length_mul
        (((List.finRange space).map fun position =>
          stackTransformCellExpression (tm := tm) (clockBits := clockBits)
            stack transform position).map TransitionExpr.gateCount)
        (stackTransformCellNodeBudget (tm := tm)) (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ := List.mem_map.mp countMem
          obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
          exact stackTransformCellExpression_gateCount_le stack transform position))
  simp only [List.length_map, List.length_finRange]
  have identity :
      space * (stackTransformCellNodeBudget (tm := tm) + 1) =
        space * stackTransformCellNodeBudget (tm := tm) + space := by ring
  omega

/-- Budget for transforming every stack of one symbolic path. -/
def stackTransformFamilyNodeBudget : Nat :=
  Fintype.card tm.K *
      (space * (stackTransformCellNodeBudget (tm := tm) + 1) + 4) + 1

/-- The stack portion of every terminal symbolic path has a uniform affine
bound. -/
theorem StatementPath.stackExpression_gateCount_le
    (path : StatementPath tm space clockBits) :
    path.stackExpression.gateCount ≤
      stackTransformFamilyNodeBudget (tm := tm) (space := space) := by
  rw [StatementPath.stackExpression, TransitionExpr.all_gateCount]
  have stackBound :
      (((finiteValues tm.K).map fun stack =>
        stackTransformExpression (tm := tm) (space := space)
          (clockBits := clockBits) stack (path.transforms stack)).map
            TransitionExpr.gateCount).sum ≤
        Fintype.card tm.K *
          (space * (stackTransformCellNodeBudget (tm := tm) + 1) + 3) := by
    simpa only [List.length_map, finiteValues_length] using
      (sum_le_length_mul
        (((finiteValues tm.K).map fun stack =>
          stackTransformExpression (tm := tm) (space := space)
            (clockBits := clockBits) stack (path.transforms stack)).map
              TransitionExpr.gateCount)
        (space * (stackTransformCellNodeBudget (tm := tm) + 1) + 3) (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ := List.mem_map.mp countMem
          obtain ⟨stack, _, rfl⟩ := List.mem_map.mp expressionMem
          exact stackTransformExpression_gateCount_le stack (path.transforms stack)))
  simp only [List.length_map, finiteValues_length]
  unfold stackTransformFamilyNodeBudget
  have identity : Fintype.card tm.K *
      (space * (stackTransformCellNodeBudget (tm := tm) + 1) + 4) =
      Fintype.card tm.K *
          (space * (stackTransformCellNodeBudget (tm := tm) + 1) + 3) +
        Fintype.card tm.K := by ring
  omega

/-- Uniform node budget for one terminal path of a statement. -/
def statementPathNodeBudget
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  2 * statementObservationDepth statement + 1 +
    stackTransformFamilyNodeBudget (tm := tm) (space := space) + 7

/-- Every generated terminal-path expression fits its syntactic and affine
stack-transform budget. -/
theorem StatementPath.expression_gateCount_le
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack))
    (path : StatementPath tm space clockBits)
    (pathMem : path ∈ statementPaths (space := space)
      (clockBits := clockBits) statement control transforms) :
    path.expression.gateCount ≤
      statementPathNodeBudget (tm := tm) (space := space) statement := by
  have guardBound := statementPaths_guard_gateCount_le
    statement control transforms path pathMem
  have stacksBound := path.stackExpression_gateCount_le
  rw [StatementPath.expression, TransitionExpr.all_gateCount]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil, nextLabelIs, nextControlIs,
    TransitionExpr.next, TransitionExpr.gateCount]
  unfold statementPathNodeBudget
  omega

/-- Node budget for the disjunction of all terminal paths from one control
state and one statement. -/
def statementPathsNodeBudget
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  statementPathCountBudget statement *
      (statementPathNodeBudget (tm := tm) (space := space) statement + 1) + 1

theorem statementPathsExpression_gateCount_le
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (control : tm.σ)
    (transforms : ∀ stack, StackTransform (tm.Γ stack)) :
    (statementPathsExpression (space := space) (clockBits := clockBits)
      statement control transforms).gateCount ≤
      statementPathsNodeBudget (tm := tm) (space := space) statement := by
  rw [statementPathsExpression, TransitionExpr.any_gateCount]
  let paths := statementPaths (space := space) (clockBits := clockBits)
    statement control transforms
  have pathSumBound :
      ((paths.map StatementPath.expression).map
        TransitionExpr.gateCount).sum ≤
        paths.length * statementPathNodeBudget (tm := tm)
          (space := space) statement := by
    simpa only [List.length_map] using
      (sum_le_length_mul
        ((paths.map StatementPath.expression).map TransitionExpr.gateCount)
        (statementPathNodeBudget (tm := tm) (space := space) statement) (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ := List.mem_map.mp countMem
          obtain ⟨path, pathMem, rfl⟩ := List.mem_map.mp expressionMem
          exact path.expression_gateCount_le statement control transforms pathMem))
  have lengthBound := statementPaths_length_le
    (space := space) (clockBits := clockBits) statement control transforms
  change paths.length ≤ statementPathCountBudget statement at lengthBound
  have pathSumTotal :
      ((paths.map StatementPath.expression).map
        TransitionExpr.gateCount).sum ≤
        statementPathCountBudget statement *
          statementPathNodeBudget (tm := tm) (space := space) statement :=
    pathSumBound.trans (Nat.mul_le_mul_right _ lengthBound)
  dsimp only [paths] at pathSumTotal lengthBound
  simp only [List.length_map]
  unfold statementPathsNodeBudget
  have identity : statementPathCountBudget statement *
      (statementPathNodeBudget (tm := tm) (space := space) statement + 1) =
      statementPathCountBudget statement *
          statementPathNodeBudget (tm := tm) (space := space) statement +
        statementPathCountBudget statement := by ring
  omega

/-- Node budget for one statement after enumerating every fixed finite-control
value. -/
def statementNodeBudget
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) : Nat :=
  Fintype.card tm.σ *
      (statementPathsNodeBudget (tm := tm) (space := space) statement + 3) + 1

theorem statementExpression_gateCount_le
    (statement : Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    (statementExpression (tm := tm) (space := space)
      (clockBits := clockBits) statement).gateCount ≤
      statementNodeBudget (tm := tm) (space := space) statement := by
  rw [statementExpression, TransitionExpr.any_gateCount]
  let expressions := (finiteValues tm.σ).map fun control =>
    TransitionExpr.and
      (currentControlIs (tm := tm) (space := space)
        (clockBits := clockBits) control)
      (statementPathsExpression (tm := tm) (space := space)
        (clockBits := clockBits) statement control identityStackTransforms)
  have expressionSumBound :
      (expressions.map TransitionExpr.gateCount).sum ≤
        Fintype.card tm.σ *
          (statementPathsNodeBudget (tm := tm) (space := space) statement + 2) := by
    simpa only [expressions, List.length_map, finiteValues_length] using
      (sum_le_length_mul
        (((finiteValues tm.σ).map fun control =>
          .and
            (currentControlIs (tm := tm) (space := space)
              (clockBits := clockBits) control)
            (statementPathsExpression (tm := tm) (space := space)
              (clockBits := clockBits) statement control
                identityStackTransforms)).map TransitionExpr.gateCount)
        (statementPathsNodeBudget (tm := tm) (space := space) statement + 2) (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ := List.mem_map.mp countMem
          obtain ⟨control, _, rfl⟩ := List.mem_map.mp expressionMem
          simp only [TransitionExpr.gateCount]
          have pathsBound := statementPathsExpression_gateCount_le
            (tm := tm) (space := space) (clockBits := clockBits)
            statement control identityStackTransforms
          change 1 + _ + 1 ≤ _
          omega))
  change (expressions.map TransitionExpr.gateCount).sum +
    expressions.length + 1 ≤ _
  have lengthEq : expressions.length = Fintype.card tm.σ := by
    simp [expressions, finiteValues_length]
  unfold statementNodeBudget
  have identity : Fintype.card tm.σ *
      (statementPathsNodeBudget (tm := tm) (space := space) statement + 3) =
      Fintype.card tm.σ *
          (statementPathsNodeBudget (tm := tm) (space := space) statement + 2) +
        Fintype.card tm.σ := by ring
  omega

/-- Explicit affine-in-stack-width budget for the complete ordinary machine
step expression.  Its coefficients are finite constants of the fixed machine. -/
def machineStepNodeBudget : Nat :=
  (((finiteValues tm.Λ).map fun label =>
    statementNodeBudget (tm := tm) (space := space) (tm.m label) + 2).sum) +
      Fintype.card tm.Λ + 1

theorem machineStepExpression_gateCount_le :
    (machineStepExpression (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount ≤
      machineStepNodeBudget (tm := tm) (space := space) := by
  rw [machineStepExpression, TransitionExpr.any_gateCount]
  let expressions := (finiteValues tm.Λ).map fun label =>
    TransitionExpr.and
      (currentLabelIs (tm := tm) (space := space)
        (clockBits := clockBits) (some label))
      (statementExpression (tm := tm) (space := space)
        (clockBits := clockBits) (tm.m label))
  have expressionSumBound :
      (expressions.map TransitionExpr.gateCount).sum ≤
        ((finiteValues tm.Λ).map fun label =>
          statementNodeBudget (tm := tm) (space := space) (tm.m label) + 2).sum := by
    unfold expressions
    simp only [List.map_map, Function.comp_apply]
    apply sum_map_le
    intro label labelMem
    have statementBound := statementExpression_gateCount_le
      (tm := tm) (space := space) (clockBits := clockBits) (tm.m label)
    change 1 + _ + 1 ≤ _
    omega
  change (expressions.map TransitionExpr.gateCount).sum +
    expressions.length + 1 ≤ _
  have lengthEq : expressions.length = Fintype.card tm.Λ := by
    simp [expressions, finiteValues_length]
  unfold machineStepNodeBudget
  omega

/-- Complete node budget for a designated bounded-machine relation. -/
def designatedMachineNodeBudget : Nat :=
  designatedNonStepNodeBudget (tm := tm) (space := space)
      (clockBits := clockBits) +
    machineStepNodeBudget (tm := tm) (space := space)

/-- The complete designated transition expression has an explicit polynomial
budget in stack and clock width, with no residual expression-size term. -/
theorem designatedMachineResetClockExpression_gateCount_le_budget
    (initial accepting : tm.Cfg) :
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).gateCount ≤
      designatedMachineNodeBudget (tm := tm) (space := space)
        (clockBits := clockBits) := by
  apply (designatedMachineResetClockExpression_gateCount_le
    initial accepting).trans
  unfold designatedMachineNodeBudget
  exact Nat.add_le_add_left machineStepExpression_gateCount_le _

/-- Fully explicit clause bound for the designated bounded-machine CNF. -/
theorem designatedMachinePeriodicCNF_clause_length_le_budget
    (initial accepting : tm.Cfg) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).clauses.length ≤
      3 * designatedMachineNodeBudget (tm := tm) (space := space)
        (clockBits := clockBits) + 1 := by
  apply (designatedMachinePeriodicCNF_clause_length_le
    initial accepting).trans
  unfold designatedMachineNodeBudget
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 3
      (Nat.add_le_add_left machineStepExpression_gateCount_le _)) 1

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
