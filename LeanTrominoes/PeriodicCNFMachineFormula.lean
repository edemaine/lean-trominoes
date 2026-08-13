import LeanTrominoes.PeriodicCNFMachineResetRelation
import LeanTrominoes.PeriodicCNFTransitionExprFormula

/-!
# Horizontal periodic CNF for bounded TM2 computations

This file first proves that every structurally well-formed Boolean slice is
reproduced on all source atoms by canonically re-encoding its decoded semantic
state.  It then uses this fact to transfer the accepting-reset expression from
canonical encodings to arbitrary well-formed valuations and packages the
expression as a forward-local periodic CNF formula.
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

private theorem oneHotFields_currentOnly :
    (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).CurrentOnly := by
  apply TransitionExpr.CurrentOnly.all
  intro expression expressionMem
  rw [oneHotFieldExpressions, List.mem_append] at expressionMem
  rcases expressionMem with expressionMem | expressionMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at expressionMem
    rcases expressionMem with rfl | rfl
    · exact TransitionExpr.currentExactlyOne_currentOnly _
    · exact TransitionExpr.currentExactlyOne_currentOnly _
  · rw [List.mem_flatMap] at expressionMem
    obtain ⟨stack, _, expressionMem⟩ := expressionMem
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp expressionMem
    exact TransitionExpr.currentExactlyOne_currentOnly _

private theorem stackSuffixExpression_currentOnly (stack : tm.K)
    (index : Nat) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).CurrentOnly := by
  unfold stackSuffixExpression
  split
  · exact ⟨TransitionExpr.current_currentOnly _,
      TransitionExpr.current_currentOnly _⟩
  · trivial

private theorem stackSuffixFields_currentOnly :
    (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).CurrentOnly := by
  apply TransitionExpr.CurrentOnly.all
  intro expression expressionMem
  rw [allStackSuffixExpressions, List.mem_flatMap] at expressionMem
  obtain ⟨stack, _, expressionMem⟩ := expressionMem
  rw [stackSuffixExpressions] at expressionMem
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp expressionMem
  exact stackSuffixExpression_currentOnly stack index

private theorem wellFormedFields_currentOnly :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).CurrentOnly :=
  ⟨oneHotFields_currentOnly, stackSuffixFields_currentOnly⟩

/-- Structural well-formedness depends only on the current endpoint. -/
theorem wellFormedFields_eval_self_iff (currentValues nextValues : Nat → Bool) :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval currentValues nextValues = true ↔
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval currentValues currentValues = true := by
  rw [wellFormedFields_currentOnly.eval_eq currentValues nextValues currentValues]

/-- The numeric clock reconstructed from a fixed-width slice has exactly the
original bits. -/
theorem BoundedMachineSlice.clockValue_testBit
    (slice : BoundedMachineSlice tm space clockBits)
    (position : Fin clockBits) :
    slice.clockValue.testBit position.val = slice.clock position := by
  let bits := (List.finRange clockBits).map slice.clock
  have bitsLength : bits.length = clockBits := by simp [bits]
  have reconstructed := TransitionExpr.fixedBits_bitsValue bits
  have pointwise := congrArg (fun values => values[position.val]?) reconstructed
  simpa [TransitionExpr.fixedBits, BoundedMachineSlice.clockValue,
    bits, bitsLength] using pointwise

/-- The clock reconstructed from any fixed-width slice lies in the represented
numeric range. -/
theorem BoundedMachineSlice.clockValue_lt
    (slice : BoundedMachineSlice tm space clockBits) :
    slice.clockValue < 2 ^ clockBits := by
  simpa [BoundedMachineSlice.clockValue] using
    TransitionExpr.bitsValue_lt_two_pow_length
      ((List.finRange clockBits).map slice.clock)

/-- Canonically re-encoding a well-formed decoded slice reproduces the source
valuation on every typed bounded-machine atom. -/
theorem encode_toResetClockState_decode_code
    {valuation : Nat → Bool}
    (wellFormed : (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true)
    (atom : BoundedMachineAtom tm space clockBits) :
    encode (space := space) (clockBits := clockBits)
        ((decode (tm := tm) (space := space) (clockBits := clockBits)
          valuation).toResetClockState) (code atom) =
      valuation (code atom) := by
  have decoded := decode_of_wellFormed wellFormed
  cases atom with
  | label labelValue =>
      rw [encode_label]
      change decide ((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).label = labelValue) = _
      exact (decoded.2.1 labelValue).symm
  | state control =>
      rw [encode_state]
      change decide ((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).control = control) = _
      exact (decoded.2.2.1 control).symm
  | stack cell =>
      rcases cell with ⟨stack, position, symbol⟩
      rw [encode_stack]
      change decide ((((decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).toCfg).stk stack)[position.val]? =
          symbol) = _
      have represented := BoundedMachineSlice.toCfg_stack_getElem?_eq
        decoded.1 stack position
      rw [represented]
      exact (decoded.2.2.2.1 stack position symbol).symm
  | clock position =>
      rw [encode_clock]
      change (decode (tm := tm) (space := space)
        (clockBits := clockBits) valuation).clockValue.testBit position.val = _
      rw [BoundedMachineSlice.clockValue_testBit]
      exact (decoded.2.2.2.2 position).symm

/-- Canonically re-encoding a well-formed decoded slice agrees with the
original valuation throughout the finite source interval. -/
theorem encode_toResetClockState_decode_below
    {valuation : Nat → Bool}
    (wellFormed : (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).eval valuation valuation = true) :
    ∀ atom < atomCount (tm := tm) (space := space) (clockBits := clockBits),
      encode (space := space) (clockBits := clockBits)
          ((decode (tm := tm) (space := space) (clockBits := clockBits)
            valuation).toResetClockState) atom = valuation atom := by
  intro atom atomLt
  let typed : BoundedMachineAtom tm space clockBits :=
    (Fintype.equivFin (BoundedMachineAtom tm space clockBits)).symm
      ⟨atom, atomLt⟩
  have codeTyped : code typed = atom := by
    simp [typed, code, atomCount]
  rw [← codeTyped]
  exact encode_toResetClockState_decode_code wellFormed typed

/-- The accepting-reset expression has its intended semantics on arbitrary
well-formed source valuations, not just canonical encodings. -/
theorem machineResetClockExpression_eval_iff
    (initial : tm.Cfg) {currentValues nextValues : Nat → Bool}
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (currentWellFormed :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval currentValues currentValues = true)
    (nextWellFormed :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval nextValues nextValues = true) :
    (machineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial).eval currentValues nextValues = true ↔
      PeriodicComputation.ResetClockRelation initial tm.step
        (machineAccepts (tm := tm)) (2 ^ clockBits - 1)
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
  let expression := machineResetClockExpression (tm := tm) (space := space)
    (clockBits := clockBits) initial
  have atoms : expression.AtomsBelow
      (atomCount (tm := tm) (space := space) (clockBits := clockBits)) :=
    machineResetClockExpression_atomsBelow initial
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
  apply machineResetClockExpression_encode_iff
  · exact initialStacksFit
  · exact currentSlice.toCfg_stack_length_le
  · exact nextSlice.toCfg_stack_length_le
  · exact currentSlice.clockValue_lt
  · exact nextSlice.clockValue_lt

/-- The concrete bounded-machine formula: structurally compile the complete
accepting-reset relation and require its root at every horizontal translate. -/
def machinePeriodicCNF (initial : tm.Cfg) : PeriodicCNF Nat :=
  requireTransitionExpr
    (machineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial)
    (atomCount (tm := tm) (space := space) (clockBits := clockBits))

theorem machinePeriodicCNF_forward (initial : tm.Cfg) :
    (machinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial).IsForwardLocal :=
  requireTransitionExpr_forward _ _

theorem machinePeriodicCNF_oneDimensional (initial : tm.Cfg) :
    (machinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial).IsOneDimensional :=
  isOneDimensional_of_isForwardLocal (machinePeriodicCNF_forward initial)

theorem machinePeriodicCNF_localOnLine (initial : tm.Cfg) :
    (machinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial).IsLocalOnLine :=
  isLocalOnLine_of_isForwardLocal (machinePeriodicCNF_forward initial)

/-- Every satisfying bi-infinite formula model decodes to a genuine bounded
accepting trace of the source machine. -/
theorem acceptingTrace_of_machinePeriodicCNF_satisfiableOnLine
    (initial : tm.Cfg)
    (initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space)
    (satisfiable : (machinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial).SatisfiableOnLine) :
    Nonempty (PeriodicComputation.AcceptingTrace tm.Cfg initial tm.step
      (machineAccepts (tm := tm)) (2 ^ clockBits - 1)) := by
  let expression := machineResetClockExpression (tm := tm) (space := space)
    (clockBits := clockBits) initial
  have sourcePath : FiniteState.HasBiInfinitePath
      (fun current next => expression.eval current next = true) :=
    (requireTransitionExpr_satisfiableOnLine_iff expression
      (atomCount (tm := tm) (space := space) (clockBits := clockBits))
      (machineResetClockExpression_atomsBelow initial)).mp satisfiable
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
    dsimp [expression, machineResetClockExpression, TransitionExpr.eval] at truth
    rw [Bool.and_eq_true] at truth
    exact truth.1
  have nextWellFormedBetween :
      (wellFormedFields (tm := tm) (space := space)
        (clockBits := clockBits)).eval
          (values (index + 1)) (values (index + 1 + 1)) = true := by
    have truth := nextTruth
    dsimp [expression, machineResetClockExpression, TransitionExpr.eval] at truth
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
    (machineAccepts (tm := tm)) (2 ^ clockBits - 1)
    ((decode (tm := tm) (space := space) (clockBits := clockBits)
      (values index)).toResetClockState)
    ((decode (tm := tm) (space := space) (clockBits := clockBits)
      (values (index + 1))).toResetClockState)
  exact (machineResetClockExpression_eval_iff initial initialStacksFit
    currentWellFormed nextWellFormed).mp currentTruth

/-- A bounded accepting trace closes into a periodic Boolean model of the
compiled machine formula. -/
theorem machinePeriodicCNF_satisfiableOnLine_of_acceptingTrace
    (initial : tm.Cfg)
    (trace : PeriodicComputation.AcceptingTrace tm.Cfg initial tm.step
      (machineAccepts (tm := tm)) (2 ^ clockBits - 1))
    (stacksFit : ∀ index : Fin (trace.length + 1), ∀ stack,
      ((trace.states index).stk stack).length ≤ space) :
    (machinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial).SatisfiableOnLine := by
  let expression := machineResetClockExpression (tm := tm) (space := space)
    (clockBits := clockBits) initial
  let values : Fin (trace.length + 1) → Nat → Bool := fun index =>
    encode (space := space) (clockBits := clockBits)
      (trace.resetClockState index)
  have initialStacksFit : ∀ stack, (initial.stk stack).length ≤ space := by
    intro stack
    rw [← trace.starts]
    exact stacksFit 0 stack
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
    apply (machineResetClockExpression_encode_iff initial
      (trace.resetClockState index) (trace.resetClockState (index + 1))
      initialStacksFit (stacksFit index) (stacksFit (index + 1))
      currentClockFits nextClockFits).mpr
    exact trace.resetClockRelation index
  change (requireTransitionExpr expression
    (atomCount (tm := tm) (space := space)
      (clockBits := clockBits))).SatisfiableOnLine
  apply (requireTransitionExpr_satisfiableOnLine_iff expression
    (atomCount (tm := tm) (space := space) (clockBits := clockBits))
    (machineResetClockExpression_atomsBelow initial)).mpr
  exact FiniteState.hasBiInfinitePath_of_hasCycle directCycle

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
