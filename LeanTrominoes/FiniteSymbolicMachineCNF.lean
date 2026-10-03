/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteMachineAcceptanceCNF
import LeanTrominoes.FinitePaddedMachineSize

/-! # Symbolic initial configurations in finite machine tableaux -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing PeriodicCNF PeriodicCNF.BoundedMachineAtom
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) (space : Nat) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

def configValues (cfg : tm.Cfg) : Nat → Bool :=
  encode (space := space) (clockBits := 0) ⟨0,cfg⟩

theorem initialTest_decode (test : TransitionExpr)
    (bound : test.AtomsBelow (atomCount (tm := tm) (space := space) (clockBits := 0)))
    (values : Nat → Bool)
    (wf : (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval values values=true) :
    test.eval values values =
      test.eval (configValues tm space (decode (tm := tm) (space := space) (clockBits := 0) values).toCfg)
        (configValues tm space (decode (tm := tm) (space := space) (clockBits := 0) values).toCfg) := by
  have clockZero : (decode (tm := tm) (space := space) (clockBits := 0) values).clockValue=0 := by
    have h := BoundedMachineSlice.clockValue_lt
      (decode (tm := tm) (space := space) (clockBits := 0) values)
    simpa using h
  have agree := encode_toResetClockState_decode_below wf
  have h1 := TransitionExpr.eval_congr_current bound (next := values) agree
  have h2 := TransitionExpr.eval_congr_next bound
    (current := encode (space := space) (clockBits := 0)
      (decode (tm := tm) (space := space) (clockBits := 0) values).toResetClockState) agree
  simpa only [BoundedMachineSlice.toResetClockState,clockZero,configValues] using (h2.trans h1).symm

/-- The last time has a final-state test instead of an outgoing machine step.
At time zero both the initial-state test and the appropriate last/step test
are imposed, so zero-step computations are represented correctly. -/
def symbolicExpression (test : TransitionExpr) (final : tm.Cfg) (steps time : Nat) : TransitionExpr :=
  .and (wellFormedFields (tm := tm) (space := space) (clockBits := 0))
    (.and
      (if time=0 then test.atCurrent else .constant true)
      (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).atCurrent
       else paddedStep tm space final))

theorem symbolicExpression_atomsBelow (test : TransitionExpr) (final : tm.Cfg) (steps time : Nat)
    (bound : test.AtomsBelow (atomCount (tm := tm) (space := space) (clockBits := 0))) :
    (symbolicExpression tm space test final steps time).AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := 0)) := by
  refine ⟨wellFormedFields_atomsBelow,?_,?_⟩
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow bound
    · trivial
  · split_ifs
    · exact TransitionExpr.atCurrent_atomsBelow (currentConfigIs_atomsBelow final)
    · exact paddedStep_atomsBelow tm space final

theorem symbolicExpression_parts (test : TransitionExpr) (final : tm.Cfg) (steps time : Nat) (current next : Nat → Bool) :
    (symbolicExpression tm space test final steps time).eval current next=true ↔
    (wellFormedFields (tm := tm) (space := space) (clockBits := 0)).eval current current=true ∧
    (if time=0 then test.eval current current=true else True) ∧
    (if time=steps then (currentConfigIs (space := space) (clockBits := 0) final).eval current current=true
      else (paddedStep tm space final).eval current next=true) := by
  by_cases first : time=0 <;> by_cases last : time=steps
  all_goals simp_all [symbolicExpression,TransitionExpr.eval,TransitionExpr.atCurrent_eval,
    wellFormedFields_eval_self_iff]

def symbolicFormula (test : TransitionExpr) (final : tm.Cfg) (steps : Nat) : FiniteCNF.Formula (Nat × Nat) :=
  FiniteCNF.traceFormula (symbolicExpression tm space test final steps)
    (atomCount (tm := tm) (space := space) (clockBits := 0)) (steps+1)

/-- A bounded TM2 trace may repeat its accepting endpoint. -/
def HasSymbolicRun (test : TransitionExpr) (final : tm.Cfg) (steps : Nat) : Prop :=
  ∃ run : Nat → tm.Cfg, test.eval (configValues tm space (run 0)) (configValues tm space (run 0))=true ∧ run steps=final ∧
    (∀ time≤steps, ∀ stack, ((run time).stk stack).length≤space) ∧
    ∀ time<steps, FinitePaddedComputation.Step tm.step final (run time) (run (time+1))

theorem symbolicFormula_correct (test : TransitionExpr) (final : tm.Cfg) (steps : Nat)
    (bound : test.AtomsBelow (atomCount (tm := tm) (space := space) (clockBits := 0)))
    (finalFits : ∀ stack, (final.stk stack).length≤space) :
    FiniteCNF.Satisfiable (symbolicFormula tm space test final steps) ↔ HasSymbolicRun tm space test final steps := by
  rw [symbolicFormula,FiniteCNF.traceFormula_correct _ _ _ (fun time _ => symbolicExpression_atomsBelow tm space test final steps time bound)]
  constructor
  · rintro ⟨trace,follows⟩
    let run := fun time => (decode (tm := tm) (space := space) (clockBits := 0) (trace time)).toCfg
    have parts (time : Nat) (ht : time≤steps) :=
      (symbolicExpression_parts tm space test final steps time (trace time) (trace (time+1))).mp
        (follows time (by omega))
    have wf (time : Nat) (ht : time≤steps) := (parts time ht).1
    refine ⟨run,?_,?_,?_,?_⟩
    · rw [← initialTest_decode tm space test bound (trace 0) (wf 0 (by omega))]
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
    apply (symbolicExpression_parts tm space test final steps time (trace time) (trace (time+1))).mpr
    refine ⟨wellFormedFields_encode (state time),?_,?_⟩
    · split_ifs with zero
      · simpa only [trace,state,zero,configValues] using first
    · split_ifs with endpoint
      · apply (currentConfigIs_encode_iff (state time) (state time) final (fits time (by omega)) finalFits).mpr
        simpa only [state,endpoint] using last
      · apply (paddedStep_encode tm space final (state time) (state (time+1)) finalFits
          (fits time (by omega)) (fits (time+1) (by omega))).mpr
        exact follows time (by omega)

theorem symbolicExpression_gateCount_le (test : TransitionExpr) (final : tm.Cfg) (steps time : Nat) :
    (symbolicExpression tm space test final steps time).gateCount ≤
      paddedNodeBudget tm space + test.gateCount := by
  have base := paddedExpression_gateCount_le tm space final final steps time
  have compare : (symbolicExpression tm space test final steps time).gateCount ≤
      (paddedExpression tm space final final steps time).gateCount + test.gateCount := by
    by_cases first : time=0 <;> by_cases last : time=steps
    all_goals simp_all only [symbolicExpression,paddedExpression,ite_true,ite_false,
      TransitionExpr.gateCount,TransitionExpr.atCurrent_gateCount]
    all_goals omega
  exact compare.trans (Nat.add_le_add_right base _)

theorem symbolicFormula_length_le (test : TransitionExpr) (final : tm.Cfg) (steps : Nat) :
    (symbolicFormula tm space test final steps).length ≤
      (steps+1)*(3*(paddedTraceSlope tm*space+paddedTraceIntercept tm+test.gateCount)+1) := by
  rw [← paddedNodeBudget_affine tm space]
  exact FiniteCNF.traceFormula_length_le _ _ _ _
    (fun time _ => symbolicExpression_gateCount_le tm space test final steps time)

theorem symbolicFormula_width (test : TransitionExpr) (final : tm.Cfg) (steps : Nat) :
    FiniteCNF.WidthAtMost 3 (symbolicFormula tm space test final steps) :=
  FiniteCNF.traceFormula_width _ _ _

theorem symbolicFormula_iff_evals (test : TransitionExpr) (final : tm.Cfg) (steps : Nat)
    (bound : test.AtomsBelow (atomCount (tm := tm) (space := space) (clockBits := 0)))
    (enough : ∀ initial : tm.Cfg,
      (∀ stack, (initial.stk stack).length≤space) →
      test.eval (configValues tm space initial) (configValues tm space initial)=true →
      TM2.stackSpace initial + steps*TM2OutputLength.machinePushBound tm ≤ space)
    (finalFits : ∀ stack, (final.stk stack).length≤space) :
    FiniteCNF.Satisfiable (symbolicFormula tm space test final steps) ↔
      ∃ initial : tm.Cfg,
        (∀ stack, (initial.stk stack).length≤space) ∧
        test.eval (configValues tm space initial) (configValues tm space initial)=true ∧
        Nonempty (StateTransition.EvalsToInTime tm.step initial (some final) steps) := by
  rw [symbolicFormula_correct tm space test final steps bound finalFits]
  constructor
  · rintro ⟨run,first,last,fits,follows⟩
    exact ⟨run 0,fits 0 (by omega),first,(FinitePaddedComputation.bounded_iff_trace tm.step (run 0) final steps).mpr
      ⟨run,rfl,last,follows⟩⟩
  · rintro ⟨initial,initialFits,accepted,⟨run⟩⟩
    refine ⟨FinitePaddedComputation.paddedTrace run.toEvalsTo,?_,
      FinitePaddedComputation.paddedTrace_final _ run.steps_le_m,?_,
      fun time _ => FinitePaddedComputation.paddedTrace_step _ time⟩
    · simpa using accepted
    · intro time _ stack
      exact (paddedTrace_stack_length_le tm run time stack).trans (enough initial initialFits accepted)

end LeanTrominoes.FiniteMachineTrace
