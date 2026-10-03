/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicComputationTrace

/-! # Padding a computation to a fixed time bound

An accepting endpoint may repeat. Such a repetition cannot create acceptance
that was not already reachable within the original time bound.
-/
noncomputable section
namespace LeanTrominoes.FinitePaddedComputation
open StateTransition PeriodicComputation
variable {State : Type*}

def Step (f : State → Option State) (accept : State) (a b : State) : Prop :=
  f a=some b ∨ a=accept ∧ b=accept

def paddedTrace {f : State → Option State} {first last : State}
    (run : EvalsTo f first (some last)) (time : Nat) : State :=
  stateAt run ⟨min time run.steps,by omega⟩

@[simp] theorem paddedTrace_zero {f : State → Option State} {first last : State}
    (run : EvalsTo f first (some last)) : paddedTrace run 0=first := by
  simpa [paddedTrace] using stateAt_zero run

theorem paddedTrace_final {f : State → Option State} {first last : State}
    (run : EvalsTo f first (some last)) {time : Nat} (late : run.steps≤time) :
    paddedTrace run time=last := by
  have index : (⟨min time run.steps,by omega⟩ : Fin (run.steps+1))=Fin.last run.steps := by
    apply Fin.ext; exact Nat.min_eq_right late
  change stateAt run _=last
  rw [index]
  exact stateAt_last run

theorem paddedTrace_step {f : State → Option State} {first last : State}
    (run : EvalsTo f first (some last)) (time : Nat) :
    Step f last (paddedTrace run time) (paddedTrace run (time+1)) := by
  by_cases early : time<run.steps
  · left
    have h := stateAt_step run (⟨time,early⟩ : Fin run.steps)
    change f (stateAt run ⟨time,by omega⟩)=some (stateAt run ⟨time+1,by omega⟩) at h
    simpa only [paddedTrace,Nat.min_eq_left (show time≤run.steps by omega),
      Nat.min_eq_left (show time+1≤run.steps by omega)] using h
  · exact Or.inr ⟨paddedTrace_final run (by omega),paddedTrace_final run (by omega)⟩

theorem paddedTrace_reaches {f : State → Option State} {first last : State}
    (run : EvalsTo f first (some last)) (time : Nat) : Reaches f first (paddedTrace run time) :=
  stateAt_reaches run _

theorem evals_of_trace (f : State → Option State) (steps : Nat) (trace : Nat → State)
    (follows : ∀ time<steps, Step f (trace steps) (trace time) (trace (time+1))) :
    Nonempty (EvalsToInTime f (trace 0) (some (trace steps)) steps) := by
  classical
  induction steps generalizing trace with
  | zero => exact ⟨EvalsToInTime.refl f (trace 0)⟩
  | succ steps ih =>
    by_cases accepted : trace 0=trace (steps+1)
    · refine ⟨⟨⟨0,?_⟩,Nat.zero_le _⟩⟩
      simpa only [Function.iterate_zero_apply] using congrArg some accepted
    · have firstStep : f (trace 0)=some (trace 1) := by
        rcases follows 0 (by omega) with h|h
        · exact h
        · exact (accepted h.1).elim
      have tail : ∀ time<steps, Step f ((fun n => trace (n+1)) steps)
          ((fun n => trace (n+1)) time) ((fun n => trace (n+1)) (time+1)) := by
        intro time ht
        exact follows (time+1) (by omega)
      obtain ⟨rest⟩ := ih (fun n => trace (n+1)) tail
      have head : EvalsToInTime f (trace 0) (some (trace 1)) 1 := ⟨⟨1,firstStep⟩,Nat.le_refl _⟩
      exact ⟨EvalsToInTime.trans f 1 steps _ _ _ head rest⟩

theorem bounded_iff_trace (f : State → Option State) (first last : State) (steps : Nat) :
    Nonempty (EvalsToInTime f first (some last) steps) ↔
      ∃ trace : Nat → State, trace 0=first ∧ trace steps=last ∧
        ∀ time<steps, Step f last (trace time) (trace (time+1)) := by
  constructor
  · rintro ⟨run⟩
    exact ⟨paddedTrace run.toEvalsTo,paddedTrace_zero _,paddedTrace_final _ run.steps_le_m,
      fun time _ => paddedTrace_step _ time⟩
  · rintro ⟨trace,initial,final,follows⟩
    have h := evals_of_trace f steps trace (by simpa only [final] using follows)
    simpa only [initial,final] using h

end LeanTrominoes.FinitePaddedComputation
