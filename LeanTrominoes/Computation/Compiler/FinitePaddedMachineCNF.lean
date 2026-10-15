/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FinitePaddedMachineStep
import LeanTrominoes.Complexity.FiniteTraceCNF

/-! # Ordinary finite CNF characterizes bounded TM2 computations exactly -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

/-- The last time has a final-state test instead of an outgoing machine step.
At time zero both the initial-state test and the appropriate last/step test
are imposed, so zero-step computations are represented correctly. -/
def paddedExpression (initial final : tm.Cfg) (steps time : Nat) : TransitionExpr :=
  .and (wellFormedFields (tm := tm) (space := space) (clockBits := 0))
    (.and
      (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).atCurrent else .constant true)
      (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
       else paddedStep tm space final))

theorem paddedExpression_atomsBelow (initial final : tm.Cfg) (steps time : Nat) :
    (paddedExpression tm space initial final steps time).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  refine ⟨wellFormedFields_atomsBelow,?_,?_⟩
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow initial)
    · trivial
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow final)
    · exact paddedStep_atomsBelow tm space final

theorem paddedExpression_parts (initial final : tm.Cfg) (steps time : Nat) (current next : Nat → Bool) :
    (paddedExpression tm space initial final steps time).eval current next=true ↔
    (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval current current=true ∧
    (if time=0 then (currentConfigIs (space := space) (clockBits := 0) initial).eval current current=true else True) ∧
    (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).eval current current=true
      else (paddedStep tm space final).eval current next=true) := by
  by_cases first : time=0 <;> by_cases last : time=steps
  all_goals simp_all [paddedExpression,TransitionExpr.eval,TransitionExpr.atCurrent_eval,
    wellFormedFields_eval_self_iff]

def paddedFormula (initial final : tm.Cfg) (steps : Nat) : FiniteCNF.Formula (Nat × Nat) :=
  FiniteCNF.traceFormula (paddedExpression tm space initial final steps)
    (atomCount (tm := tm) (space := space) (clockBits := 0)) (steps+1)

/-- A bounded TM2 trace may repeat its accepting endpoint. -/
def HasPaddedRun (initial final : tm.Cfg) (steps : Nat) : Prop :=
  ∃ run : Nat → tm.Cfg, run 0=initial ∧ run steps=final ∧
    (∀ time≤steps, ∀ stack, ((run time).stk stack).length≤space) ∧
    ∀ time<steps, FinitePaddedComputation.Step tm.step final (run time) (run (time+1))

theorem paddedFormula_correct (initial final : tm.Cfg) (steps : Nat)
    (initialFits : ∀ stack, (initial.stk stack).length≤space)
    (finalFits : ∀ stack, (final.stk stack).length≤space) :
    FiniteCNF.Satisfiable (paddedFormula tm space initial final steps) ↔ HasPaddedRun tm space initial final steps := by
  rw [paddedFormula,FiniteCNF.traceFormula_correct _ _ _ (fun time _ => paddedExpression_atomsBelow tm space initial final steps time)]
  constructor
  · rintro ⟨trace,follows⟩
    let run := fun time => (decode (tm := tm) (space := space) (clockBits := 0) (trace time)).toCfg
    have parts (time : Nat) (ht : time≤steps) :=
      (paddedExpression_parts tm space initial final steps time (trace time) (trace (time+1))).mp
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
      have stepTruth : (paddedStep tm space final).eval
          (trace time) (trace (time+1))=true := by
        simpa only [if_neg (show time≠steps by omega)] using (parts time (by omega)).2.2
      exact (paddedStep_decode tm space final _ _ finalFits currentWF nextWF).mp stepTruth
  · rintro ⟨run,first,last,fits,follows⟩
    let state := fun time => (⟨0,run time⟩ : PeriodicComputation.ResetClockState tm.Cfg)
    let trace := fun time => encode (space := space) (clockBits := 0) (state time)
    refine ⟨trace,?_⟩
    intro time ht
    apply (paddedExpression_parts tm space initial final steps time (trace time) (trace (time+1))).mpr
    refine ⟨wellFormedFields_encode (state time),?_,?_⟩
    · split_ifs with zero
      · apply (currentConfigIs_encode_iff (state time) (state time) initial (fits time (by omega)) initialFits).mpr
        simpa only [state,zero] using first
    · split_ifs with endpoint
      · apply (currentConfigIs_encode_iff (state time) (state time) final (fits time (by omega)) finalFits).mpr
        simpa only [state,endpoint] using last
      · apply (paddedStep_encode tm space final (state time) (state (time+1)) finalFits
          (fits time (by omega)) (fits (time+1) (by omega))).mpr
        exact follows time (by omega)

end LeanTrominoes.FiniteMachineTrace
