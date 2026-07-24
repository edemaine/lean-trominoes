import LeanTrominoes.PartrecEvaluatorSpaceRefinement
import LeanTrominoes.PartrecFlatIteration

/-!
# Space certificates for tail-style iteration

This module lifts the semantic flat countdown from
`PartrecFlatIteration` to the evaluator-space interface.  The reusable rule
isolates one iteration of the fixed-point body: if each such body trace and
its returned value fit a common budget, then arbitrarily many tail-recursive
iterations fit the same budget.
-/

namespace Turing
namespace PartrecToTM2

open StateTransition

/-- The tagged value returned by one flat countdown body call. -/
def flatCountdownOutput
    (step : List Nat → List Nat) :
    Nat → List Nat → List Nat
  | 0, payload => 0 :: payload
  | remaining + 1, payload =>
      1 :: remaining :: step payload

/-- The uniform obligations for one iteration of a flat countdown under its
fixed-point continuation.  `trace` is restricted to the finite segment
ending where the body result enters that continuation. -/
structure FlatCountdownBodyFits
    (stepCode : ToPartrec.Code)
    (step : List Nat → List Nat)
    (continuation : ToPartrec.Cont)
    (bound : Nat) : Prop where
  normal :
    ∀ remaining payload,
      normalSimulationSpace
          (ToPartrec.Code.flatCountdownBody stepCode)
          (.fix (ToPartrec.Code.flatCountdownBody stepCode)
            continuation)
          (remaining :: payload) ≤
        bound
  trace :
    ∀ remaining payload current,
      Reaches ToPartrec.step
          (ToPartrec.stepNormal
            (ToPartrec.Code.flatCountdownBody stepCode)
            (.fix (ToPartrec.Code.flatCountdownBody stepCode)
              continuation)
            (remaining :: payload))
          current →
      Reaches ToPartrec.step current
          (ToPartrec.stepRet
            (.fix (ToPartrec.Code.flatCountdownBody stepCode)
              continuation)
            (flatCountdownOutput step remaining payload)) →
      cfgSimulationSpace current ≤ bound
  returned :
    ∀ remaining payload,
      encodedListSpace
          (flatCountdownOutput step remaining payload) +
          continuationSpace
            (.fix (ToPartrec.Code.flatCountdownBody stepCode)
              continuation) ≤
        bound

/-- A uniformly fitted body gives the entire tail-recursive countdown the
same space budget, independent of the number of iterations. -/
theorem EvaluatorCallFits.flatIterate
    {stepCode : ToPartrec.Code}
    {step : List Nat → List Nat}
    {continuation : ToPartrec.Cont}
    {bound steps : Nat} {payload : List Nat}
    (stepCorrect :
      ∀ values, stepCode.eval values = pure (step values))
    (body :
      FlatCountdownBodyFits stepCode step continuation bound)
    (after :
      EvaluatorExecutionFits bound
        (.ret continuation ((step^[steps]) payload))) :
    EvaluatorCallFits
      (ToPartrec.Code.flatIterate stepCode)
      continuation (steps :: payload) bound := by
  rw [ToPartrec.Code.flatIterate]
  apply EvaluatorCallFits.fix
  induction steps generalizing payload with
  | zero =>
      have fixedAfter :
          EvaluatorExecutionFits bound
            (.ret
              (.fix
                (ToPartrec.Code.flatCountdownBody stepCode)
                continuation)
              (flatCountdownOutput step 0 payload)) := by
        apply EvaluatorExecutionFits.ret_fix_zero
        · rfl
        · exact body.returned 0 payload
        · simpa [flatCountdownOutput] using after
      apply EvaluatorCallFits.of_trace
      · rw [ToPartrec.Code.flatCountdownBody_zero_eval]
        exact Part.mem_some _
      · exact body.normal 0 payload
      · exact fixedAfter
      · exact body.trace 0 payload
  | succ remaining induction =>
      have recursiveAfter :
          EvaluatorExecutionFits bound
            (.ret continuation
              ((step^[remaining]) (step payload))) := by
        simpa [Function.iterate_succ_apply] using after
      have recursiveBody :=
        induction (payload := step payload) recursiveAfter
      have fixedAfter :
          EvaluatorExecutionFits bound
            (.ret
              (.fix
                (ToPartrec.Code.flatCountdownBody stepCode)
                continuation)
              (flatCountdownOutput step (remaining + 1)
                payload)) := by
        apply EvaluatorExecutionFits.ret_fix_succ
        · simp [flatCountdownOutput]
        · exact body.returned (remaining + 1) payload
        · simpa [flatCountdownOutput] using recursiveBody
      apply EvaluatorCallFits.of_trace
      · rw [ToPartrec.Code.flatCountdownBody_succ_eval
          stepCode step stepCorrect]
        exact Part.mem_some _
      · exact body.normal (remaining + 1) payload
      · exact fixedAfter
      · exact body.trace (remaining + 1) payload

end PartrecToTM2
end Turing
