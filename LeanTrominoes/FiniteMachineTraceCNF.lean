/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteMachineTraceExpression
import LeanTrominoes.FiniteTraceCNF

/-! # Ordinary finite CNF characterizes bounded TM2 computations exactly -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

theorem expression_parts (initial final : tm.Cfg) (steps time : Nat) (current next : Nat → Bool) :
    (expression tm space initial final steps time).eval current next=true ↔
    (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval current current=true ∧
    (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).eval current current=true else True) ∧
    (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).eval current current=true
      else (machineStepExpression (tm := tm) (space := space) (clockBits := 0)).eval current next=true) := by
  by_cases first : time=0 <;> by_cases last : time=steps
  all_goals simp_all [expression,TransitionExpr.eval,TransitionExpr.atCurrent_eval,
    wellFormedFields_eval_self_iff]

def formula (initial final : tm.Cfg) (steps : Nat) : FiniteCNF.Formula (Nat × Nat) :=
  FiniteCNF.traceFormula (expression tm space initial final steps)
    (atomCount (tm := tm) (space := space) (clockBits := 0)) (steps+1)

/-- The semantic witness is a real TM2 computation with bounded stacks.
There is no reset edge and no periodicity assumption. -/
def HasRun (initial final : tm.Cfg) (steps : Nat) : Prop :=
  ∃ run : Nat → tm.Cfg, run 0=initial ∧ run steps=final ∧
    (∀ time≤steps, ∀ stack, ((run time).stk stack).length≤space) ∧
    ∀ time<steps, tm.step (run time)=some (run (time+1))

theorem formula_correct (initial final : tm.Cfg) (steps : Nat)
    (initialFits : ∀ stack, (initial.stk stack).length≤space)
    (finalFits : ∀ stack, (final.stk stack).length≤space) :
    FiniteCNF.Satisfiable (formula tm space initial final steps) ↔ HasRun tm space initial final steps := by
  rw [formula,FiniteCNF.traceFormula_correct _ _ _ (fun time _ => expression_atomsBelow tm space initial final steps time)]
  constructor
  · rintro ⟨trace,follows⟩
    let run := fun time => (decode (tm := tm) (space := space) (clockBits := 0) (trace time)).toCfg
    have parts (time : Nat) (ht : time≤steps) :=
      (expression_parts tm space initial final steps time (trace time) (trace (time+1))).mp
        (follows time (by omega))
    have wf (time : Nat) (ht : time≤steps) := (parts time ht).1
    refine ⟨run,?_,?_,?_,?_⟩
    · apply (currentConfig_decode tm space initial (trace 0) initialFits (wf 0 (by omega))).mp
      simpa using (parts 0 (by omega)).2.1
    · apply (currentConfig_decode tm space final (trace steps) finalFits (wf steps (by omega))).mp
      simpa using (parts steps (by omega)).2.2
    · intro time _ stack
      exact BoundedMachineSlice.toCfg_stack_length_le _ stack
    · intro time ht
      have currentWF := wf time (by omega)
      have nextWF := wf (time+1) (by omega)
      have currentOneHot : (oneHotFields (tm := tm) (space := space) (clockBits := 0)).eval
          (trace time) (trace time)=true := by
        have parts := currentWF
        simp only [wellFormedFields,TransitionExpr.eval,Bool.and_eq_true] at parts
        exact parts.1
      have nextOneHot : (oneHotFields (tm := tm) (space := space) (clockBits := 0)).eval
          (trace (time+1)) (trace (time+1))=true := by
        have parts := nextWF
        simp only [wellFormedFields,TransitionExpr.eval,Bool.and_eq_true] at parts
        exact parts.1
      have stepTruth : (machineStepExpression (tm := tm) (space := space) (clockBits := 0)).eval
          (trace time) (trace (time+1))=true := by
        simpa only [if_neg (show time≠steps by omega)] using (parts time (by omega)).2.2
      exact (machineStepExpression_eval_iff_step currentOneHot nextOneHot
        (decode_of_wellFormed currentWF).1 (decode_of_wellFormed nextWF).1).mp stepTruth
  · rintro ⟨run,first,last,fits,follows⟩
    let state := fun time => (⟨0,run time⟩ : PeriodicComputation.ResetClockState tm.Cfg)
    let trace := fun time => encode (space := space) (clockBits := 0) (state time)
    refine ⟨trace,?_⟩
    intro time ht
    apply (expression_parts tm space initial final steps time (trace time) (trace (time+1))).mpr
    refine ⟨wellFormedFields_encode (state time),?_,?_⟩
    · split_ifs with zero
      · apply (currentConfigIs_encode_iff (state time) (state time) initial (fits time (by omega)) initialFits).mpr
        simpa only [state,zero] using first
    · split_ifs with endpoint
      · apply (currentConfigIs_encode_iff (state time) (state time) final (fits time (by omega)) finalFits).mpr
        simpa only [state,endpoint] using last
      · apply (machineStepExpression_encode_iff (state time) (state (time+1))
          (fits time (by omega)) (fits (time+1) (by omega))).mpr
        exact follows time (by omega)

end LeanTrominoes.FiniteMachineTrace
