import LeanTrominoes.Complexity
import LeanTrominoes.PeriodicComputationCycle

/-!
# Extracting explicit traces from terminating computations

Mathlib's `StateTransition.EvalsTo` records only a step count and an iterate
equation.  The periodic-CNF compiler instead consumes an indexed list of all
configurations.  This file reconstructs that list, proves its consecutive-step
equations, and specializes the construction to finite TM2 computations.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicComputation

open StateTransition
open Turing

private theorem iterate_none {State : Type*}
    (transition : State → Option State) (steps : Nat) :
    (flip bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      change (flip bind transition)^[steps] none = none
      exact induction

theorem existsStateAt {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (index : Nat) (indexLe : index ≤ run.steps) :
    ∃ state, (flip bind transition)^[index] (some first) = some state := by
  cases equality : (flip bind transition)^[index] (some first) with
  | none =>
      have stepsEq : run.steps = (run.steps - index) + index := by omega
      have final := run.evals_in_steps
      rw [stepsEq, Function.iterate_add_apply, equality,
        iterate_none] at final
      cases final
  | some state => exact ⟨state, rfl⟩

/-- The configuration reached at a bounded prefix of a terminating run. -/
def stateAt {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (index : Fin (run.steps + 1)) : State :=
  Classical.choose (existsStateAt run index.val (by omega))

theorem stateAt_iterate {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (index : Fin (run.steps + 1)) :
    (flip bind transition)^[index.val] (some first) =
      some (stateAt run index) :=
  Classical.choose_spec (existsStateAt run index.val (by omega))

@[simp]
theorem stateAt_zero {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last)) :
    stateAt run 0 = first := by
  have atZero := stateAt_iterate run (0 : Fin (run.steps + 1))
  simpa using atZero.symm

@[simp]
theorem stateAt_last {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last)) :
    stateAt run (Fin.last run.steps) = last := by
  have atLast := stateAt_iterate run (Fin.last run.steps)
  have final := run.evals_in_steps
  simp only [Fin.val_last] at atLast
  rw [final] at atLast
  exact Option.some.inj atLast.symm

theorem stateAt_step {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (index : Fin run.steps) :
    transition (stateAt run index.castSucc) =
      some (stateAt run index.succ) := by
  have current := stateAt_iterate run index.castSucc
  have next := stateAt_iterate run index.succ
  have successorValue : index.succ.val = index.castSucc.val + 1 := by simp
  rw [successorValue, Function.iterate_succ_apply', current] at next
  exact next

/-- Every bounded prefix state of a terminating run is reachable from its
initial state. -/
theorem stateAt_reaches {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (index : Fin (run.steps + 1)) :
    Reaches transition first (stateAt run index) := by
  have reachable : ∀ value (valueLt : value < run.steps + 1),
      Reaches transition first (stateAt run ⟨value, valueLt⟩) := by
    intro value
    induction value with
    | zero =>
        intro valueLt
        have indexEq : (⟨0, valueLt⟩ : Fin (run.steps + 1)) = 0 :=
          Fin.ext rfl
        rw [indexEq, stateAt_zero]
        exact Relation.ReflTransGen.refl
    | succ value induction =>
        intro valueLt
        have beforeLt : value < run.steps + 1 := by omega
        let stepIndex : Fin run.steps := ⟨value, by omega⟩
        apply Relation.ReflTransGen.tail (induction beforeLt)
        have beforeEq : (⟨value, beforeLt⟩ : Fin (run.steps + 1)) =
            stepIndex.castSucc := by
          apply Fin.ext
          simp [stepIndex]
        have afterEq : (⟨value + 1, valueLt⟩ : Fin (run.steps + 1)) =
            stepIndex.succ := by
          apply Fin.ext
          simp [stepIndex]
        rw [beforeEq, afterEq]
        exact stateAt_step run stepIndex
  exact reachable index.val index.isLt

/-- The endpoint of a terminating counted run is reachable. -/
theorem evalsTo_reaches {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last)) :
    Reaches transition first last := by
  simpa using stateAt_reaches run (Fin.last run.steps)

/-- Determinism makes a terminal state reachable from one start unique. -/
theorem eq_of_reachable_terminals {State : Type*}
    {transition : State → Option State} {first left right : State}
    (leftReachable : Reaches transition first left)
    (rightReachable : Reaches transition first right)
    (leftTerminal : transition left = none)
    (rightTerminal : transition right = none) :
    left = right := by
  rcases reaches_total leftReachable rightReachable with
      leftToRight | rightToLeft
  · have rightEqLeft := (Relation.reflTransGen_iff_eq
      (r := fun before after => after ∈ transition before)
      (a := left) (b := right) (fun next nextStep => by
        change transition left = some next at nextStep
        rw [leftTerminal] at nextStep
        contradiction)).mp leftToRight
    exact rightEqLeft.symm
  · exact (Relation.reflTransGen_iff_eq
      (r := fun before after => after ∈ transition before)
      (a := right) (b := left) (fun next nextStep => by
        change transition right = some next at nextStep
        rw [rightTerminal] at nextStep
        contradiction)).mp rightToLeft

/-- A terminating deterministic run never repeats a configuration before its
terminal endpoint. -/
theorem stateAt_injective {State : Type*}
    {transition : State → Option State} {first last : State}
    (run : EvalsTo transition first (some last))
    (terminal : transition last = none) :
    Function.Injective (stateAt run) := by
  intro firstIndex secondIndex stateEq
  wlog order : firstIndex.val ≤ secondIndex.val generalizing firstIndex secondIndex
  · exact (this (firstIndex := secondIndex) (secondIndex := firstIndex)
      stateEq.symm (by omega)).symm
  apply Fin.ext
  by_contra valueNe
  have firstLtSecond : firstIndex.val < secondIndex.val := by omega
  let remaining := run.steps - secondIndex.val
  have stepsEq : run.steps = remaining + secondIndex.val := by
    dsimp only [remaining]
    omega
  have suffixFromSecond :
      (flip bind transition)^[remaining]
          (some (stateAt run secondIndex)) = some last := by
    have final := run.evals_in_steps
    rw [stepsEq, Function.iterate_add_apply,
      stateAt_iterate run secondIndex] at final
    exact final
  have prefixAtRepeated :
      (flip bind transition)^[remaining + firstIndex.val] (some first) =
        some last := by
    rw [Function.iterate_add_apply, stateAt_iterate run firstIndex,
      stateEq, suffixFromSecond]
  let beforeTerminal : Fin run.steps :=
    ⟨remaining + firstIndex.val, by
      dsimp only [remaining]
      omega⟩
  have represented := stateAt_iterate run beforeTerminal.castSucc
  have representedValue : beforeTerminal.castSucc.val =
      remaining + firstIndex.val := by rfl
  rw [representedValue, prefixAtRepeated] at represented
  have stateTerminal : stateAt run beforeTerminal.castSucc = last :=
    Option.some.inj represented.symm
  have nextStep := stateAt_step run beforeTerminal
  rw [stateTerminal, terminal] at nextStep
  cases nextStep

/-- A terminating computation whose terminal state is accepting and whose
accepting states cannot step yields the explicit bounded trace required by the
reset-clock construction. -/
theorem acceptingTrace_of_evalsTo {State : Type*}
    {transition : State → Option State} {first last : State}
    {accepts : State → Prop} {limit : Nat}
    (run : EvalsTo transition first (some last))
    (lengthLe : run.steps ≤ limit)
    (acceptsLast : accepts last)
    (acceptingTerminal : ∀ state, accepts state → transition state = none) :
    Nonempty (AcceptingTrace State first transition accepts limit) := by
  refine ⟨
    { length := run.steps
      length_le := lengthLe
      states := stateAt run
      starts := stateAt_zero run
      accepts_last := by simpa using acceptsLast
      not_accepts := ?_
      steps := stateAt_step run }⟩
  intro index accepted
  have step := stateAt_step run index
  rw [acceptingTerminal _ accepted] at step
  cases step

/-- Every state explicitly listed by an accepting trace is reachable from its
initial state. -/
theorem AcceptingTrace.reaches {State : Type*}
    {first : State} {transition : State → Option State}
    {accepts : State → Prop} {limit : Nat}
    (trace : AcceptingTrace State first transition accepts limit)
    (index : Fin (trace.length + 1)) :
    Reaches transition first (trace.states index) := by
  have reachable : ∀ value (valueLt : value < trace.length + 1),
      Reaches transition first (trace.states ⟨value, valueLt⟩) := by
    intro value
    induction value with
    | zero =>
        intro valueLt
        have indexEq : (⟨0, valueLt⟩ : Fin (trace.length + 1)) = 0 :=
          Fin.ext rfl
        rw [indexEq, trace.starts]
        exact Relation.ReflTransGen.refl
    | succ value induction =>
        intro valueLt
        have beforeLt : value < trace.length + 1 := by omega
        let stepIndex : Fin trace.length := ⟨value, by omega⟩
        apply Relation.ReflTransGen.tail (induction beforeLt)
        have beforeEq : (⟨value, beforeLt⟩ : Fin (trace.length + 1)) =
            stepIndex.castSucc := by
          apply Fin.ext
          simp [stepIndex]
        have afterEq : (⟨value + 1, valueLt⟩ : Fin (trace.length + 1)) =
            stepIndex.succ := by
          apply Fin.ext
          simp [stepIndex]
        rw [beforeEq, afterEq]
        exact trace.steps stepIndex
  exact reachable index.val index.isLt

/-- A finite TM2 output computation gives an accepting trace whose final
condition is precisely the halted (`none`) control label. -/
theorem machineAcceptingTrace_of_evalsTo {tm : FinTM2}
    {initial terminal : tm.Cfg} {limit : Nat}
    (run : EvalsTo tm.step initial (some terminal))
    (lengthLe : run.steps ≤ limit)
    (terminalHalted : terminal.l = none) :
    Nonempty (AcceptingTrace tm.Cfg initial tm.step
      (fun config => config.l = none) limit) := by
  apply acceptingTrace_of_evalsTo run lengthLe terminalHalted
  intro config halted
  rcases config with ⟨label, state, stackContents⟩
  simp only at halted
  subst label
  rfl

/-- One stack is no larger than the total configuration-space measure. -/
theorem stack_length_le_configurationSpace (tm : FinTM2)
    (configuration : tm.Cfg) (stack : tm.K) :
    (configuration.stk stack).length ≤
      Complexity.configurationSpace tm configuration := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.K := tm.kFin
  unfold Complexity.configurationSpace
  exact Finset.single_le_sum
    (f := fun stack => (configuration.stk stack).length)
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ stack)

/-- Every state of a trace starting from a certified polynomial-space
decider input respects the decider's global polynomial space bound, hence so
does each individual stack. -/
theorem AcceptingTrace.stacksFit_decider
    {Input : Type} {encoding : Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (input : Input) {accepts : decider.tm.Cfg → Prop} {limit : Nat}
    (trace : AcceptingTrace decider.tm.Cfg
      (initList decider.tm
        (List.map decider.inputAlphabet.invFun (encoding.encode input)))
      decider.tm.step accepts limit)
    (index : Fin (trace.length + 1)) (stack : decider.tm.K) :
    ((trace.states index).stk stack).length ≤
      decider.space.eval (encoding.encode input).length := by
  apply (stack_length_le_configurationSpace decider.tm
    (trace.states index) stack).trans
  exact decider.space_le input (trace.states index) (trace.reaches index)

end PeriodicComputation

end LeanTrominoes
