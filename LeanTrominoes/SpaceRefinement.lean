import LeanTrominoes.PartrecPolySpace

/-!
# Space-aware deterministic refinements

`StateTransition.Reaches` forgets both the number of deterministic steps and
the intermediate configurations.  Space refinements need that missing
information: a macro step may be implemented by many low-level steps, and
every one of them must satisfy the space bound.

This module records a deterministic run together with a bound on every prefix.
It also proves the comparison lemma needed to alternate bounded low-level
segments: any other run from the same state either ends inside the recorded
segment (and is bounded) or extends beyond its endpoint.
-/

namespace StateTransition

/-- A deterministic run from `first` to `last` whose every prefix ending in a
live state satisfies `space ≤ bound`. -/
structure EvalsToInSpace {state : Type*}
    (transition : state → Option state) (space : state → Nat)
    (bound : Nat) (first last : state)
    extends EvalsTo transition first (some last) where
  space_le :
    ∀ steps configuration,
      steps ≤ toEvalsTo.steps →
      (flip bind transition)^[steps] (some first) =
        some configuration →
      space configuration ≤ bound

namespace EvalsToInSpace

theorem first_le {state : Type*} {transition : state → Option state}
    {space : state → Nat} {bound : Nat} {first last : state}
    (run : EvalsToInSpace transition space bound first last) :
    space first ≤ bound := by
  apply run.space_le 0 first (Nat.zero_le _)
  rfl

theorem last_le {state : Type*} {transition : state → Option state}
    {space : state → Nat} {bound : Nat} {first last : state}
    (run : EvalsToInSpace transition space bound first last) :
    space last ≤ bound := by
  apply run.space_le run.steps last (Nat.le_refl _)
  exact run.evals_in_steps

/-- A zero-step run is space-bounded precisely by its initial state. -/
def refl {state : Type*} (transition : state → Option state)
    (space : state → Nat) (bound : Nat) (first : state)
    (bounded : space first ≤ bound) :
    EvalsToInSpace transition space bound first first where
  toEvalsTo := EvalsTo.refl transition first
  space_le := by
    intro steps configuration stepsBound equality
    have stepsBound' : steps ≤ 0 := by
      simpa [EvalsTo.refl] using stepsBound
    have stepsZero : steps = 0 := by omega
    subst steps
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at equality
    subst configuration
    exact bounded

/-- One deterministic step whose two endpoints fit the budget. -/
def single {state : Type*} {transition : state → Option state}
    {space : state → Nat} {bound : Nat} {first last : state}
    (step : transition first = some last)
    (firstBound : space first ≤ bound)
    (lastBound : space last ≤ bound) :
    EvalsToInSpace transition space bound first last where
  toEvalsTo :=
    { steps := 1
      evals_in_steps := by
        simp only [Function.iterate_one]
        change transition first = some last
        exact step }
  space_le := by
    intro steps configuration stepsBound equality
    have stepsCases : steps = 0 ∨ steps = 1 := by omega
    rcases stepsCases with rfl | rfl
    · simp only [Function.iterate_zero, id_eq,
        Option.some.injEq] at equality
      subst configuration
      exact firstBound
    · simp only [Function.iterate_one] at equality
      change transition first = some configuration at equality
      rw [step] at equality
      cases equality
      exact lastBound

/-- Enlarge the budget of a recorded run. -/
def mono {state : Type*} {transition : state → Option state}
    {space : state → Nat} {small large : Nat} {first last : state}
    (run : EvalsToInSpace transition space small first last)
    (budget : small ≤ large) :
    EvalsToInSpace transition space large first last where
  toEvalsTo := run.toEvalsTo
  space_le := by
    intro steps configuration stepsBound equality
    exact (run.space_le steps configuration stepsBound equality).trans budget

/-- Concatenate two runs that use the same space budget. -/
def trans {state : Type*} {transition : state → Option state}
    {space : state → Nat} {bound : Nat} {first middle last : state}
    (before : EvalsToInSpace transition space bound first middle)
    (after : EvalsToInSpace transition space bound middle last) :
    EvalsToInSpace transition space bound first last where
  toEvalsTo :=
    EvalsTo.trans transition first middle (some last)
      before.toEvalsTo after.toEvalsTo
  space_le := by
    intro steps configuration stepsBound equality
    by_cases insideBefore : steps ≤ before.steps
    · exact before.space_le steps configuration insideBefore equality
    · let afterSteps := steps - before.steps
      have stepsEq : steps = afterSteps + before.steps := by
        dsimp only [afterSteps]
        omega
      have afterStepsBound : afterSteps ≤ after.steps := by
        change steps ≤ after.steps + before.steps at stepsBound
        dsimp only [afterSteps]
        omega
      apply after.space_le afterSteps configuration afterStepsBound
      have beforeEquality :
          (flip bind transition)^[before.steps] (some first) =
            some middle :=
        before.evals_in_steps
      rw [stepsEq, Function.iterate_add_apply,
        beforeEquality] at equality
      exact equality

private theorem reaches_of_iterate_eq {state : Type*}
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

/-- Compare an arbitrary deterministic run with a recorded bounded segment.
If the arbitrary endpoint is not a prefix of the segment, the segment's
endpoint reaches it. -/
theorem space_le_or_reaches {state : Type*}
    {transition : state → Option state} {space : state → Nat}
    {bound : Nat} {first middle last : state}
    (segment : EvalsToInSpace transition space bound first middle)
    (run : Reaches transition first last) :
    space last ≤ bound ∨ Reaches transition middle last := by
  let counted := Turing.EvalsTo.of_reaches run
  by_cases isPrefix : counted.steps ≤ segment.steps
  · left
    exact segment.space_le counted.steps last isPrefix
      counted.evals_in_steps
  · right
    let remaining := counted.steps - segment.steps
    apply reaches_of_iterate_eq transition remaining middle last
    have countedEquality :
        (flip bind transition)^[counted.steps] (some first) =
          some last :=
      counted.evals_in_steps
    have segmentEquality :
        (flip bind transition)^[segment.steps] (some first) =
          some middle :=
      segment.evals_in_steps
    have stepsEq :
        counted.steps = remaining + segment.steps := by
      dsimp only [remaining]
      omega
    rw [stepsEq, Function.iterate_add_apply,
      segmentEquality] at countedEquality
    exact countedEquality

/-- Once a bounded recorded run reaches a terminal state, every configuration
reachable from the same start is one of its bounded prefixes. -/
theorem space_le_of_terminal {state : Type*}
    {transition : state → Option state} {space : state → Nat}
    {bound : Nat} {first terminal configuration : state}
    (segment :
      EvalsToInSpace transition space bound first terminal)
    (terminalStep : transition terminal = none)
    (run : Reaches transition first configuration) :
    space configuration ≤ bound := by
  rcases segment.space_le_or_reaches run with bounded | afterTerminal
  · exact bounded
  · have configurationEq : configuration = terminal := by
      apply
        (Relation.reflTransGen_iff_eq
          (r := fun before after => after ∈ transition before)
          (fun next nextStep => by
            change transition terminal = some next at nextStep
            rw [terminalStep] at nextStep
            cases nextStep)).mp
      exact afterTerminal
    subst configuration
    exact segment.last_le

end EvalsToInSpace
end StateTransition
