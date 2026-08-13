import LeanTrominoes.PeriodicCNFMachineFormula
import LeanTrominoes.PeriodicCNFMachineConfigurationCount

/-!
# Horizontal machine CNF with a designated accepting output

Both Boolean outputs of a total decider are halted configurations.  For a
many-one reduction, reset edges must therefore recognize the particular
terminal configuration encoding `true`, not merely a halted label.  This file
packages that designated-acceptance relation as a local 1D periodic CNF and
proves both directions of its trace semantics.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

noncomputable local instance : DecidableEq tm.Λ := Classical.decEq _
noncomputable local instance : DecidableEq tm.σ := Classical.decEq _
noncomputable local instance (stack : tm.K) : DecidableEq (tm.Γ stack) :=
  Classical.decEq _

/-- Designated accepting-reset semantics on arbitrary well-formed source
valuations. -/
theorem designatedMachineResetClockExpression_eval_iff
    (initial accepting : tm.Cfg) {currentValues nextValues : Nat → Bool}
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (acceptingStacksFit : ∀ stack, (accepting.stk stack).length ≤ space)
    (currentWellFormed :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextWellFormed :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval nextValues nextValues = true) :
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).eval
        currentValues nextValues = true ↔
      PeriodicComputation.ResetClockRelation initial tm.step
        (designatedMachineAccepts accepting) (2 ^ clockBits - 1)
        ((decode (tm := tm) (space := space) (clockBits := clockBits)
          currentValues).toResetClockState)
        ((decode (tm := tm) (space := space) (clockBits := clockBits)
          nextValues).toResetClockState) := by
  let currentSlice := decode (tm := tm) (space := space)
    (clockBits := clockBits) currentValues
  let nextSlice := decode (tm := tm) (space := space)
    (clockBits := clockBits) nextValues
  let currentState := currentSlice.toResetClockState
  let nextState := nextSlice.toResetClockState
  let expression := designatedMachineResetClockExpression (tm := tm)
    (space := space) (clockBits := clockBits) initial accepting
  have atoms : expression.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
    designatedMachineResetClockExpression_atomsBelow initial accepting
  have currentAgree := encode_toResetClockState_decode_below currentWellFormed
  have nextAgree := encode_toResetClockState_decode_below nextWellFormed
  have evalEq : expression.eval currentValues nextValues =
      expression.eval
        (encode (space := space) (clockBits := clockBits) currentState)
        (encode (space := space) (clockBits := clockBits) nextState) := by
    calc
      expression.eval currentValues nextValues =
          expression.eval
            (encode (space := space) (clockBits := clockBits) currentState)
            nextValues :=
        TransitionExpr.eval_congr_current atoms
          (fun atom atomLt => (currentAgree atom atomLt).symm)
      _ = expression.eval
          (encode (space := space) (clockBits := clockBits) currentState)
          (encode (space := space) (clockBits := clockBits) nextState) :=
        TransitionExpr.eval_congr_next atoms
          (fun atom atomLt => (nextAgree atom atomLt).symm)
  rw [evalEq]
  apply designatedMachineResetClockExpression_encode_iff
  · exact initialStacksFit
  · exact acceptingStacksFit
  · exact currentSlice.toCfg_stack_length_le
  · exact nextSlice.toCfg_stack_length_le
  · exact currentSlice.clockValue_lt
  · exact nextSlice.clockValue_lt

/-- Compiled local 1D formula accepting exactly cycles through one designated
terminal configuration. -/
def designatedMachinePeriodicCNF (initial accepting : tm.Cfg) :
    PeriodicCNF Nat :=
  requireTransitionExpr
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting)
    (atomCount (tm := tm) (space := space) (clockBits := clockBits))

theorem designatedMachinePeriodicCNF_forward (initial accepting : tm.Cfg) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).IsForwardLocal :=
  requireTransitionExpr_forward _ _

theorem designatedMachinePeriodicCNF_oneDimensional
    (initial accepting : tm.Cfg) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).IsOneDimensional :=
  isOneDimensional_of_isForwardLocal
    (designatedMachinePeriodicCNF_forward initial accepting)

theorem designatedMachinePeriodicCNF_localOnLine
    (initial accepting : tm.Cfg) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).IsLocalOnLine :=
  isLocalOnLine_of_isForwardLocal
    (designatedMachinePeriodicCNF_forward initial accepting)

theorem acceptingTrace_of_designatedMachinePeriodicCNF_satisfiableOnLine
    (initial accepting : tm.Cfg)
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (acceptingStacksFit : ∀ stack, (accepting.stk stack).length ≤ space)
    (satisfiable : (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).SatisfiableOnLine) :
    Nonempty (PeriodicComputation.AcceptingTrace tm.Cfg initial tm.step
      (designatedMachineAccepts accepting) (2 ^ clockBits - 1)) := by
  let expression := designatedMachineResetClockExpression (tm := tm)
    (space := space) (clockBits := clockBits) initial accepting
  have sourcePath : FiniteState.HasBiInfinitePath
      (fun current next => expression.eval current next = true) :=
    (requireTransitionExpr_satisfiableOnLine_iff expression
      (atomCount (tm := tm) (space := space) (clockBits := clockBits))
      (designatedMachineResetClockExpression_atomsBelow
        initial accepting)).mp satisfiable
  obtain ⟨values, follows⟩ := sourcePath
  let states : Int → PeriodicComputation.ResetClockState tm.Cfg := fun index =>
    (decode (tm := tm) (space := space) (clockBits := clockBits)
      (values index)).toResetClockState
  apply PeriodicComputation.acceptingTrace_of_hasBiInfinitePath
  refine ⟨states, ?_⟩
  intro index
  have currentTruth := follows index
  have nextTruth := follows (index + 1)
  have currentWellFormedBetween :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval
          (values index) (values (index + 1)) = true := by
    have truth := currentTruth
    dsimp [expression, designatedMachineResetClockExpression,
      TransitionExpr.eval] at truth
    rw [Bool.and_eq_true] at truth
    exact truth.1
  have nextWellFormedBetween :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval
          (values (index + 1)) (values (index + 1 + 1)) = true := by
    have truth := nextTruth
    dsimp [expression, designatedMachineResetClockExpression,
      TransitionExpr.eval] at truth
    rw [Bool.and_eq_true] at truth
    exact truth.1
  have currentWellFormed :=
    (wellFormedFields_eval_self_iff (tm := tm) (space := space)
      (clockBits := clockBits) (values index) (values (index + 1))).mp
      currentWellFormedBetween
  have nextWellFormed :=
    (wellFormedFields_eval_self_iff (tm := tm) (space := space)
      (clockBits := clockBits) (values (index + 1))
        (values (index + 1 + 1))).mp nextWellFormedBetween
  change PeriodicComputation.ResetClockRelation initial tm.step
    (designatedMachineAccepts accepting) (2 ^ clockBits - 1)
    ((decode (tm := tm) (space := space) (clockBits := clockBits)
      (values index)).toResetClockState)
    ((decode (tm := tm) (space := space) (clockBits := clockBits)
      (values (index + 1))).toResetClockState)
  exact (designatedMachineResetClockExpression_eval_iff
    initial accepting initialStacksFit acceptingStacksFit
    currentWellFormed nextWellFormed).mp currentTruth

theorem designatedMachinePeriodicCNF_satisfiableOnLine_of_acceptingTrace
    (initial accepting : tm.Cfg)
    (trace : PeriodicComputation.AcceptingTrace tm.Cfg initial tm.step
      (designatedMachineAccepts accepting) (2 ^ clockBits - 1))
    (stacksFit : ∀ index : Fin (trace.length + 1), ∀ stack,
      ((trace.states index).stk stack).length ≤ space) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).SatisfiableOnLine := by
  let expression := designatedMachineResetClockExpression (tm := tm)
    (space := space) (clockBits := clockBits) initial accepting
  let values : Fin (trace.length + 1) → Nat → Bool := fun index =>
    encode (space := space) (clockBits := clockBits)
      (trace.resetClockState index)
  have initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space := by
    intro stack
    rw [← trace.starts]
    exact stacksFit 0 stack
  have acceptingStacksFit : ∀ stack,
      (accepting.stk stack).length ≤ space := by
    intro stack
    rw [← trace.accepts_last]
    exact stacksFit (Fin.last trace.length) stack
  have directCycle : FiniteState.HasCycle
      (fun current next => expression.eval current next = true) := by
    refine ⟨trace.length, values, ?_⟩
    intro index
    have currentClockFits : (trace.resetClockState index).clock <
        2 ^ clockBits := by
      change index.val < 2 ^ clockBits
      have indexBound := index.isLt
      have traceBound := trace.length_le
      have powerPositive : 0 < 2 ^ clockBits := by positivity
      omega
    have nextClockFits : (trace.resetClockState (index + 1)).clock <
        2 ^ clockBits := by
      change (index + 1).val < 2 ^ clockBits
      have indexBound := (index + 1).isLt
      have traceBound := trace.length_le
      have powerPositive : 0 < 2 ^ clockBits := by positivity
      omega
    change expression.eval
      (encode (space := space) (clockBits := clockBits)
        (trace.resetClockState index))
      (encode (space := space) (clockBits := clockBits)
        (trace.resetClockState (index + 1))) = true
    apply (designatedMachineResetClockExpression_encode_iff
      initial accepting (trace.resetClockState index)
      (trace.resetClockState (index + 1)) initialStacksFit
      acceptingStacksFit (stacksFit index) (stacksFit (index + 1))
      currentClockFits nextClockFits).mpr
    exact trace.resetClockRelation index
  change (requireTransitionExpr expression
    (atomCount (tm := tm) (space := space)
      (clockBits := clockBits))).SatisfiableOnLine
  apply (requireTransitionExpr_satisfiableOnLine_iff expression
    (atomCount (tm := tm) (space := space) (clockBits := clockBits))
    (designatedMachineResetClockExpression_atomsBelow
      initial accepting)).mpr
  exact FiniteState.hasBiInfinitePath_of_hasCycle directCycle

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
