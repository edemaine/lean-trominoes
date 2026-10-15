/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteMachineTraceSize
import LeanTrominoes.Computation.Compiler.FinitePaddedMachineCNF
import LeanTrominoes.SAT.CNF.FiniteCNFWidth
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFMachineStepAffine

/-! # Explicit polynomial size of finite machine trace paddedFormulas -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def paddedNodeBudget : Nat := wellFormedNodeBudget (tm := tm) (space := space)+
  4*fixedConfigNodeCount (tm := tm) (space := space)+machineStepNodeBudget (tm := tm) (space := space)+6

theorem paddedExpression_gateCount_le (initial final : tm.Cfg) (steps time : Nat) :
    (paddedExpression tm space initial final steps time).gateCount≤paddedNodeBudget tm space := by
  have wf := wellFormedFields_gateCount_le (tm := tm) (space := space) (clockBits := 0)
  have stepBound := machineStepExpression_gateCount_le (tm := tm) (space := space) (clockBits := 0)
  have paddedBound : (paddedStep tm space final).gateCount ≤
      machineStepNodeBudget (tm := tm) (space := space)+
        2*fixedConfigNodeCount (tm := tm) (space := space)+2 := by
    simp only [paddedStep,TransitionExpr.gateCount,TransitionExpr.atCurrent_gateCount,
      TransitionExpr.atNext_gateCount,currentConfigIs_gateCount,fixedConfigNodeCount]
    omega
  have startBound :
      (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).atCurrent else .constant true).gateCount≤
        fixedConfigNodeCount (tm := tm) (space := space)+1 := by
    split_ifs <;> simp [TransitionExpr.atCurrent_gateCount,TransitionExpr.gateCount,fixedConfigNodeCount]
  have endBound :
      (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
       else paddedStep tm space final).gateCount≤
        3*fixedConfigNodeCount (tm := tm) (space := space)+machineStepNodeBudget (tm := tm) (space := space)+3 := by
    split_ifs
    · simp [TransitionExpr.atCurrent_gateCount,fixedConfigNodeCount]; omega
    · omega
  change _+(_+_+1)+1≤_
  change _≤wellFormedNodeBudget (tm := tm) (space := space) at wf
  unfold paddedNodeBudget
  omega

def paddedTraceSlope : Nat := Fintype.card tm.K*(oneHotFieldNodeBudget (tm := tm)+14)+machineStepSlope (tm := tm)
def paddedTraceIntercept : Nat := 2*oneHotFieldNodeBudget (tm := tm)+31+8*Fintype.card tm.K+machineStepIntercept (tm := tm)

theorem paddedNodeBudget_affine : paddedNodeBudget tm space=paddedTraceSlope tm*space+paddedTraceIntercept tm := by
  simp only [paddedNodeBudget,wellFormedNodeBudget,fixedConfigNodeCount,machineStepNodeBudget_eq_affine,
    paddedTraceSlope,paddedTraceIntercept]
  ring

theorem paddedFormula_length_le (initial final : tm.Cfg) (steps : Nat) :
    (paddedFormula tm space initial final steps).length≤
      (steps+1)*(3*(paddedTraceSlope tm*space+paddedTraceIntercept tm)+1) := by
  rw [← paddedNodeBudget_affine tm space]
  exact FiniteCNF.traceFormula_length_le _ _ _ _ (fun time _ => paddedExpression_gateCount_le tm space initial final steps time)

theorem paddedFormula_width (initial final : tm.Cfg) (steps : Nat) :
    FiniteCNF.WidthAtMost 3 (paddedFormula tm space initial final steps) := FiniteCNF.traceFormula_width _ _ _

end LeanTrominoes.FiniteMachineTrace
