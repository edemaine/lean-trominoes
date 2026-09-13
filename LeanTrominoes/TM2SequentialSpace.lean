/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TM2SequentialMachine
import LeanTrominoes.SpaceRefinement

/-! # Workspace bounds for sequential machine composition -/

noncomputable section
namespace LeanTrominoes.TM2SequentialMachine
open Turing StateTransition
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

@[simp] theorem first_space (first second : FinTM2) (Middle : Type)
    (c : first.Cfg) : TM2.stackSpace (liftFirstCfg first second Middle c) = TM2.stackSpace c := by
  unfold TM2.stackSpace
  rw [← (Stack.proxyTypeEquiv first.K second.K).sum_comp]
  simp [liftFirstCfg, firstStacks, Stack.proxyTypeEquiv]

@[simp] theorem second_space (first second : FinTM2) (Middle : Type)
    (c : second.Cfg) : TM2.stackSpace (liftSecondCfg first second Middle c) = TM2.stackSpace c := by
  unfold TM2.stackSpace
  rw [← (Stack.proxyTypeEquiv first.K second.K).sum_comp]
  simp [liftSecondCfg, secondStacks, Stack.proxyTypeEquiv]

private theorem none_iterate {S : Type} (step : S → Option S) (n : Nat) :
    (flip bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih

theorem prefix_some {S : Type} (step : S → Option S) {a b : S}
    (run : EvalsTo step a (some b)) (n : Nat) (hn : n ≤ run.steps) :
    ∃ c, (flip bind step)^[n] (some a) = some c := by
  cases h : (flip bind step)^[n] (some a) with
  | some c => exact ⟨c,rfl⟩
  | none =>
    have he := run.evals_in_steps
    have count : run.steps = (run.steps-n)+n := by omega
    rw [count,Function.iterate_add_apply,h,none_iterate] at he
    cases he

/-- A step-preserving embedding preserves a recorded space bound. -/
def liftSpace {S T : Type} (source : S → Option S) (target : T → Option T)
    (ss : S → Nat) (ts : T → Nat) (lift : S → T)
    (stepLift : ∀ {a b}, source a = some b → target (lift a) = some (lift b))
    (spaceLift : ∀ c, ts (lift c) = ss c)
    {budget : Nat} {a b : S} (run : EvalsToInSpace source ss budget a b) :
    EvalsToInSpace target ts budget (lift a) (lift b) where
  steps := run.steps
  evals_in_steps := lift_iterate source target lift stepLift run.steps a b run.evals_in_steps
  space_le := by
    intro n c hn he
    obtain ⟨d,hd⟩ := prefix_some source run.toEvalsTo n hn
    have lifted := lift_iterate source target lift stepLift n a d hd
    rw [lifted] at he
    cases he
    rw [spaceLift]
    exact run.space_le n d hn hd

/-- A timed segment uses at most its initial space plus its push allowance. -/
def spaceOfTime (m : FinTM2) {a b : m.Cfg} {time : Nat}
    (run : EvalsToInTime m.step a (some b) time) :
    EvalsToInSpace m.step TM2.stackSpace
      (TM2.stackSpace a + time * TM2OutputLength.machinePushBound m) a b where
  toEvalsTo := run.toEvalsTo
  space_le := by
    intro n c hn he
    exact (TM2OutputLength.iterate_stackSpace_le m n a c he).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hn.trans run.steps_le_m)) _)

theorem reaches_of_iterate_eq {state : Type*}
    (transition : state → Option state) :
    ∀ steps first last,
      (flip bind transition)^[steps] (some first) =
          some last →
        Reaches transition first last := by
  intro steps
  induction steps with
  | zero =>
      intro first last equality
      simp only [Function.iterate_zero, id_eq,
        Option.some.injEq] at equality
      subst last
      exact Relation.ReflTransGen.refl
  | succ steps induction =>
      intro first last equality
      rw [Function.iterate_succ_apply] at equality
      cases nextStep : transition first with
      | none =>
          have firstStep :
              flip bind transition (some first) = none := by
            exact nextStep
          have noneIterate :
              ∀ count,
                (flip bind transition)^[count] none = none := by
            intro count
            induction count with
            | zero => rfl
            | succ count induction =>
                rw [Function.iterate_succ_apply]
                rw [show flip bind transition none = none from rfl]
                exact induction
          rw [firstStep, noneIterate] at equality
          cases equality
      | some next =>
          have firstToNext :
              next ∈ transition first := by
            simp only [Option.mem_def]
            exact nextStep
          have firstStep :
              flip bind transition (some first) = some next :=
            nextStep
          exact Relation.ReflTransGen.head firstToNext
            (induction next last (by
              rw [firstStep] at equality
              exact equality))


variable {AΓ BΓ CΓ : Type} [Fintype BΓ]
    (first : TM2ComputableAux AΓ BΓ) (second : TM2ComputableAux BΓ CΓ)

def liftFirstSpace {a b : first.tm.Cfg} {budget : Nat}
    (run : EvalsToInSpace first.tm.step TM2.stackSpace budget a b) :
    EvalsToInSpace (machine first second).step TM2.stackSpace budget
      (liftFirstCfg first.tm second.tm BΓ a) (liftFirstCfg first.tm second.tm BΓ b) :=
  liftSpace _ _ _ _ _ (liftFirst_step first second) (first_space _ _ _) run

def liftSecondSpace {a b : second.tm.Cfg} {budget : Nat}
    (run : EvalsToInSpace second.tm.step TM2.stackSpace budget a b) :
    EvalsToInSpace (machine first second).step TM2.stackSpace budget
      (liftSecondCfg first.tm second.tm BΓ a) (liftSecondCfg first.tm second.tm BΓ b) :=
  liftSpace _ _ _ _ _ (liftSecond_step first second) (second_space _ _ _) run


/-- Exact space certificate for a timed preprocessing run followed by a
space-bounded computation. The bridge is charged by its linear running time. -/
def compositionSpaceRun (input : List AΓ) (middle : List BΓ) (output : List CΓ)
    (time budget : Nat)
    (frontRun : TM2OutputsInTime first.tm (input.map first.inputAlphabet.invFun)
      (some (middle.map first.outputAlphabet.invFun)) time)
    (backRun : EvalsToInSpace second.tm.step TM2.stackSpace budget
      (initList second.tm (middle.map second.inputAlphabet.invFun))
      (haltList second.tm (output.map second.outputAlphabet.invFun))) :
    EvalsToInSpace (machine first second).step TM2.stackSpace
      (input.length + time * TM2OutputLength.machinePushBound first.tm +
        (middle.length + (4*middle.length+2)*TM2OutputLength.machinePushBound (machine first second)) + budget)
      (initList (machine first second) (input.map first.inputAlphabet.invFun))
      (haltList (machine first second) (output.map second.outputAlphabet.invFun)) := by
  let front := liftFirstSpace first second (spaceOfTime first.tm frontRun)
  let bridge := spaceOfTime (machine first second) (bridgeRun first second middle)
  let back := liftSecondSpace first second backRun
  have frontBound : TM2.stackSpace (initList first.tm (input.map first.inputAlphabet.invFun)) = input.length := by
    simp [TM2OutputLength.stackSpace_initList]
  have bridgeBound : TM2.stackSpace
      (liftFirstCfg first.tm second.tm BΓ (haltList first.tm (middle.map first.outputAlphabet.invFun))) = middle.length := by
    simp [TM2OutputLength.stackSpace_haltList]
  let total := input.length + time * TM2OutputLength.machinePushBound first.tm +
    (middle.length + (4*middle.length+2)*TM2OutputLength.machinePushBound (machine first second)) + budget
  let frontLarge := front.mono (large := total) (by rw [frontBound]; dsimp [total]; omega)
  let bridgeLarge := bridge.mono (large := total) (by
    change TM2.stackSpace (liftFirstCfg first.tm second.tm BΓ
      (haltList first.tm (middle.map first.outputAlphabet.invFun))) + _ ≤ total
    rw [bridgeBound]; dsimp [total]; omega)
  let backLarge := back.mono (large := total) (by dsimp [total]; omega)
  rw [initList_machine_eq_liftFirst,haltList_machine_eq_liftSecond]
  exact (frontLarge.trans bridgeLarge).trans backLarge

end LeanTrominoes.TM2SequentialMachine
