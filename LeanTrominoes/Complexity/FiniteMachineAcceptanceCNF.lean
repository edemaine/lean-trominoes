/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Compiler.FinitePaddedMachineCNF
import LeanTrominoes.Computation.TM2.TM2OutputLength

/-! # Finite CNF for acceptance within a time bound -/
noncomputable section
namespace LeanTrominoes.FiniteMachineTrace
open Turing StateTransition PeriodicComputation FinitePaddedComputation
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin
variable (tm : FinTM2) [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

theorem paddedTrace_stack_length_le {initial final : tm.Cfg} {steps : Nat}
    (run : EvalsToInTime tm.step initial (some final) steps) (time : Nat) (stack : tm.K) :
    ((paddedTrace run.toEvalsTo time).stk stack).length ≤
      TM2.stackSpace initial + steps * TM2OutputLength.machinePushBound tm := by
  classical
  have h := TM2OutputLength.iterate_stackSpace_le tm (min time run.steps) initial
    (paddedTrace run.toEvalsTo time) (stateAt_iterate run.toEvalsTo ⟨min time run.steps,by omega⟩)
  have single : ((paddedTrace run.toEvalsTo time).stk stack).length ≤
      TM2.stackSpace (paddedTrace run.toEvalsTo time) := by
    unfold TM2.stackSpace
    exact Finset.single_le_sum (f := fun k => ((paddedTrace run.toEvalsTo time).stk k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ stack)
  exact single.trans (h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ ((Nat.min_le_right _ _).trans run.steps_le_m)) _))

/-- With enough space for every computation prefix, the tableau characterizes
acceptance by the deadline, including zero-step and early acceptance. -/
theorem paddedFormula_iff_evals (space : Nat) (initial final : tm.Cfg) (steps : Nat)
    (enough : TM2.stackSpace initial + steps * TM2OutputLength.machinePushBound tm ≤ space)
    (finalFits : ∀ stack, (final.stk stack).length≤space) :
    FiniteCNF.Satisfiable (paddedFormula tm space initial final steps) ↔
      Nonempty (EvalsToInTime tm.step initial (some final) steps) := by
  classical
  have initialFits (stack : tm.K) : (initial.stk stack).length≤space := by
    have single : (initial.stk stack).length≤TM2.stackSpace initial := by
      unfold TM2.stackSpace
      exact Finset.single_le_sum (f := fun k => (initial.stk k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ stack)
    omega
  rw [paddedFormula_correct tm space initial final steps initialFits finalFits]
  constructor
  · rintro ⟨trace,first,last,_,follows⟩
    exact (bounded_iff_trace tm.step initial final steps).mpr ⟨trace,first,last,follows⟩
  · rintro ⟨run⟩
    exact ⟨paddedTrace run.toEvalsTo,paddedTrace_zero _,paddedTrace_final _ run.steps_le_m,
      fun time _ stack => (paddedTrace_stack_length_le tm run time stack).trans enough,
      fun time _ => paddedTrace_step _ time⟩

end LeanTrominoes.FiniteMachineTrace
