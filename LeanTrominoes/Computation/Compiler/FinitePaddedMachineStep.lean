/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Complexity.FiniteMachineTraceCNF
import LeanTrominoes.Computation.Compiler.FinitePaddedComputation

/-! # Accepting self-loops in finite machine tableaux -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def paddedStep (final : tm.Cfg) : TransitionExpr :=
  .or (machineStepExpression (tm := tm) (space := space) (clockBits := 0))
    (.and (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
      (currentConfigIs (space := space) (clockBits := 0) final).atNext)

theorem paddedStep_atomsBelow (final : tm.Cfg) :
    (paddedStep tm space final).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) :=
  ⟨machineStepExpression_atomsBelow,
    TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow final),
    TransitionExpr.atNext_atomsBelow (currentConfigIs_atomsBelow final)⟩

theorem paddedStep_decode (final : tm.Cfg) (current next : Nat → Bool)
    (fit : ∀ stack, (final.stk stack).length≤space)
    (currentWF : (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval current current=true)
    (nextWF : (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval next next=true) :
    (paddedStep tm space final).eval current next=true ↔
      FinitePaddedComputation.Step tm.step final
        (decode (tm := tm) (space := space) (clockBits := 0) current).toCfg
        (decode (tm := tm) (space := space) (clockBits := 0) next).toCfg := by
  have currentOneHot := currentWF
  have nextOneHot := nextWF
  simp only [wellFormedFields,TransitionExpr.eval,Bool.and_eq_true] at currentOneHot nextOneHot
  simp only [paddedStep,TransitionExpr.eval,TransitionExpr.atCurrent_eval,
    TransitionExpr.atNext_eval,Bool.or_eq_true,Bool.and_eq_true,FinitePaddedComputation.Step]
  rw [machineStepExpression_eval_iff_step currentOneHot.1 nextOneHot.1
    (decode_of_wellFormed currentWF).1 (decode_of_wellFormed nextWF).1,
    currentConfig_decode tm space final current fit currentWF,
    currentConfig_decode tm space final next fit nextWF]

theorem paddedStep_encode (final : tm.Cfg)
    (current next : PeriodicComputation.ResetClockState tm.Cfg)
    (fit : ∀ stack, (final.stk stack).length≤space)
    (currentFits : ∀ stack, (current.config.stk stack).length≤space)
    (nextFits : ∀ stack, (next.config.stk stack).length≤space) :
    (paddedStep tm space final).eval
      (encode (space := space) (clockBits := 0) current)
      (encode (space := space) (clockBits := 0) next)=true ↔
      FinitePaddedComputation.Step tm.step final current.config next.config := by
  simp only [paddedStep,TransitionExpr.eval,TransitionExpr.atCurrent_eval,
    TransitionExpr.atNext_eval,Bool.or_eq_true,Bool.and_eq_true,FinitePaddedComputation.Step]
  rw [machineStepExpression_encode_iff current next currentFits nextFits,
    currentConfigIs_encode_iff current current final currentFits fit,
    currentConfigIs_encode_iff next next final nextFits fit]

end LeanTrominoes.FiniteMachineTrace
