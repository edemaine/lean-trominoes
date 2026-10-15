/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteMachineTraceCNF
import LeanTrominoes.SAT.CNF.FiniteCNFWidth
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFMachineStepAffine

/-! # Explicit polynomial size of finite machine trace formulas -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def nodeBudget : Nat := wellFormedNodeBudget (tm := tm) (space := space)+
  2*fixedConfigNodeCount (tm := tm) (space := space)+machineStepNodeBudget (tm := tm) (space := space)+4

theorem expression_gateCount_le (initial final : tm.Cfg) (steps time : Nat) :
    (expression tm space initial final steps time).gateCount≤nodeBudget tm space := by
  have wf := wellFormedFields_gateCount_le (tm := tm) (space := space) (clockBits := 0)
  have stepBound := machineStepExpression_gateCount_le (tm := tm) (space := space) (clockBits := 0)
  have startBound :
      (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).atCurrent else .constant true).gateCount≤
        fixedConfigNodeCount (tm := tm) (space := space)+1 := by
    split_ifs <;> simp [TransitionExpr.atCurrent_gateCount,TransitionExpr.gateCount,fixedConfigNodeCount]
  have endBound :
      (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
       else machineStepExpression (tm := tm) (space := space) (clockBits := 0)).gateCount≤
        fixedConfigNodeCount (tm := tm) (space := space)+machineStepNodeBudget (tm := tm) (space := space)+1 := by
    split_ifs
    · simp [TransitionExpr.atCurrent_gateCount,fixedConfigNodeCount]; omega
    · omega
  change _+(_+_+1)+1≤_
  change _≤wellFormedNodeBudget (tm := tm) (space := space) at wf
  unfold nodeBudget
  omega

def traceSlope : Nat := Fintype.card tm.K*(oneHotFieldNodeBudget (tm := tm)+10)+machineStepSlope (tm := tm)
def traceIntercept : Nat := 2*oneHotFieldNodeBudget (tm := tm)+19+4*Fintype.card tm.K+machineStepIntercept (tm := tm)

theorem nodeBudget_affine : nodeBudget tm space=traceSlope tm*space+traceIntercept tm := by
  simp only [nodeBudget,wellFormedNodeBudget,fixedConfigNodeCount,machineStepNodeBudget_eq_affine,
    traceSlope,traceIntercept]
  ring

theorem formula_length_le (initial final : tm.Cfg) (steps : Nat) :
    (formula tm space initial final steps).length≤
      (steps+1)*(3*(traceSlope tm*space+traceIntercept tm)+1) := by
  rw [← nodeBudget_affine tm space]
  exact FiniteCNF.traceFormula_length_le _ _ _ _ (fun time _ => expression_gateCount_le tm space initial final steps time)

theorem formula_width (initial final : tm.Cfg) (steps : Nat) :
    FiniteCNF.WidthAtMost 3 (formula tm space initial final steps) := FiniteCNF.traceFormula_width _ _ _

end LeanTrominoes.FiniteMachineTrace
