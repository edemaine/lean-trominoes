/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFMachineDesignatedFormula
import LeanTrominoes.PeriodicCNFTransitionExprSize

/-!
# Quantitative size bounds for bounded machine formulas

This file counts the finite source vocabulary and bounds the structural
components of a bounded TM2 slice.  All constants depend only on the fixed
machine; the represented stack width and reset-clock width remain explicit.
-/

noncomputable section

open scoped BigOperators

namespace LeanTrominoes

namespace PeriodicCNF

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace BoundedMachineAtom

variable {tm : FinTM2} {space clockBits : Nat}
variable [stackFinite : ∀ stack, Fintype (tm.Γ stack)]

private theorem sum_map_constant {Value : Type*} (values : List Value)
    (function : Value → Nat) (constant : Nat)
    (constantValue : ∀ value, function value = constant) :
    (values.map function).sum = values.length * constant := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp [constantValue, ih, Nat.succ_mul]
      omega

private theorem sum_le_length_mul (values : List Nat) (bound : Nat)
    (bounded : ∀ value ∈ values, value ≤ bound) :
    values.sum ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.sum_cons, List.length_cons]
      calc
        value + values.sum ≤ bound + values.length * bound :=
          Nat.add_le_add (bounded value (by simp))
            (ih (fun member memberMem => bounded member (by simp [memberMem])))
        _ = (values.length + 1) * bound := by ring

/-- Number of one-hot stack-cell bits per represented position, summed over
the fixed machine's stacks. -/
def stackCellBitRate : Nat :=
  ∑ stack : tm.K, Fintype.card (Option (tm.Γ stack))

/-- A uniform cardinality bound for every one-hot field in a slice. -/
def fieldCardBudget : Nat :=
  Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
    stackCellBitRate (tm := tm)

/-- The source vocabulary is affine in stack width and clock width. -/
theorem atomCount_eq :
    atomCount (tm := tm) (space := space) (clockBits := clockBits) =
      Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        space * stackCellBitRate (tm := tm) + clockBits := by
  classical
  rw [atomCount_eq_card_sum]
  simp [stackCellBitRate, Finset.mul_sum]
  ac_rfl

/-- Configuration bits omit the reset clock and are affine in stack width. -/
theorem configurationBitCount_eq :
    configurationBitCount (tm := tm) (space := space) =
      Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
        space * stackCellBitRate (tm := tm) := by
  simp [configurationBitCount, atomCount_eq]

private theorem label_card_le_fieldCardBudget :
    Fintype.card (Option tm.Λ) ≤ fieldCardBudget (tm := tm) := by
  unfold fieldCardBudget
  omega

private theorem state_card_le_fieldCardBudget :
    Fintype.card tm.σ ≤ fieldCardBudget (tm := tm) := by
  unfold fieldCardBudget
  omega

private theorem stack_card_le_stackCellBitRate (stack : tm.K) :
    Fintype.card (Option (tm.Γ stack)) ≤ stackCellBitRate (tm := tm) := by
  classical
  unfold stackCellBitRate
  exact Finset.single_le_sum
    (f := fun candidate : tm.K => Fintype.card (Option (tm.Γ candidate)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ stack)

private theorem stack_card_le_fieldCardBudget (stack : tm.K) :
    Fintype.card (Option (tm.Γ stack)) ≤ fieldCardBudget (tm := tm) := by
  exact (stack_card_le_stackCellBitRate stack).trans (by
    unfold fieldCardBudget
    omega)

/-- Number of exact-one fields in a bounded slice. -/
@[simp]
theorem oneHotFieldExpressions_length :
    (oneHotFieldExpressions (tm := tm) (space := space)
      (clockBits := clockBits)).length =
      2 + Fintype.card tm.K * space := by
  classical
  simp [oneHotFieldExpressions, finiteValues_length]
  omega

private theorem oneHotFieldExpression_gateCount_le
    {expression : TransitionExpr}
    (member : expression ∈
      oneHotFieldExpressions (tm := tm) (space := space)
        (clockBits := clockBits)) :
    expression.gateCount ≤
      4 * (fieldCardBudget (tm := tm) + 1) ^ 2 := by
  classical
  rw [oneHotFieldExpressions, List.mem_append] at member
  rcases member with fixed | stackField
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
    rcases fixed with rfl | rfl
    · apply (TransitionExpr.currentExactlyOne_gateCount_le _).trans
      rw [labelAtoms_length]
      nlinarith [label_card_le_fieldCardBudget (tm := tm)]
    · apply (TransitionExpr.currentExactlyOne_gateCount_le _).trans
      rw [stateAtoms_length]
      nlinarith [state_card_le_fieldCardBudget (tm := tm)]
  · rw [List.mem_flatMap] at stackField
    obtain ⟨stack, _, stackField⟩ := stackField
    obtain ⟨position, _, rfl⟩ := List.mem_map.mp stackField
    apply (TransitionExpr.currentExactlyOne_gateCount_le _).trans
    rw [stackCellAtoms_length]
    nlinarith [stack_card_le_fieldCardBudget (tm := tm) stack]

/-- Uniform quadratic budget for one finite exact-one field. -/
def oneHotFieldNodeBudget : Nat :=
  4 * (fieldCardBudget (tm := tm) + 1) ^ 2

/-- The complete exact-one structural expression is affine in represented
stack width. -/
theorem oneHotFields_gateCount_le :
    (oneHotFields (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount ≤
      (2 + Fintype.card tm.K * space) *
          (oneHotFieldNodeBudget (tm := tm) + 1) + 1 := by
  rw [oneHotFields, TransitionExpr.all_gateCount]
  have sumBound :
      ((oneHotFieldExpressions (tm := tm) (space := space)
        (clockBits := clockBits)).map TransitionExpr.gateCount).sum ≤
        (oneHotFieldExpressions (tm := tm) (space := space)
          (clockBits := clockBits)).length *
          oneHotFieldNodeBudget (tm := tm) := by
    simpa only [List.length_map] using
      (sum_le_length_mul
        ((oneHotFieldExpressions (tm := tm) (space := space)
          (clockBits := clockBits)).map TransitionExpr.gateCount)
        (oneHotFieldNodeBudget (tm := tm)) (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ :=
            List.mem_map.mp countMem
          exact oneHotFieldExpression_gateCount_le expressionMem))
  rw [oneHotFieldExpressions_length] at sumBound ⊢
  calc
    _ ≤ (2 + Fintype.card tm.K * space) *
          oneHotFieldNodeBudget (tm := tm) +
        (2 + Fintype.card tm.K * space) + 1 := by omega
    _ = (2 + Fintype.card tm.K * space) *
          (oneHotFieldNodeBudget (tm := tm) + 1) + 1 := by ring

private theorem stackSuffixExpression_gateCount_le
    (stack : tm.K) (index : Nat) :
    (stackSuffixExpression (space := space) (clockBits := clockBits)
      stack index).gateCount ≤ 4 := by
  unfold stackSuffixExpression stackNoneAtom
  split <;> simp [TransitionExpr.current, TransitionExpr.gateCount]

/-- Number of adjacent suffix constraints across all represented stacks. -/
@[simp]
theorem allStackSuffixExpressions_length :
    (allStackSuffixExpressions (tm := tm) (space := space)
      (clockBits := clockBits)).length = Fintype.card tm.K * space := by
  classical
  simp [allStackSuffixExpressions, stackSuffixExpressions,
    finiteValues_length]

/-- Stack list-shape constraints are affine in represented stack width. -/
theorem stackSuffixFields_gateCount_le :
    (stackSuffixFields (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount ≤
      5 * (Fintype.card tm.K * space) + 1 := by
  rw [stackSuffixFields, TransitionExpr.all_gateCount]
  have sumBound :
      ((allStackSuffixExpressions (tm := tm) (space := space)
        (clockBits := clockBits)).map TransitionExpr.gateCount).sum ≤
        (allStackSuffixExpressions (tm := tm) (space := space)
          (clockBits := clockBits)).length * 4 := by
    simpa only [List.length_map] using
      (sum_le_length_mul
        ((allStackSuffixExpressions (tm := tm) (space := space)
          (clockBits := clockBits)).map TransitionExpr.gateCount) 4 (by
          intro count countMem
          obtain ⟨expression, expressionMem, rfl⟩ :=
            List.mem_map.mp countMem
          rw [allStackSuffixExpressions, List.mem_flatMap] at expressionMem
          obtain ⟨stack, _, expressionMem⟩ := expressionMem
          rw [stackSuffixExpressions] at expressionMem
          obtain ⟨index, _, rfl⟩ := List.mem_map.mp expressionMem
          exact stackSuffixExpression_gateCount_le stack index))
  rw [allStackSuffixExpressions_length] at sumBound ⊢
  calc
    _ ≤ (Fintype.card tm.K * space) * 4 +
        Fintype.card tm.K * space + 1 := by omega
    _ = 5 * (Fintype.card tm.K * space) + 1 := by ring

/-- All current-slice tests for one fixed stack use two nodes per cell plus
the terminal conjunction constant. -/
@[simp]
theorem currentStackIs_gateCount (target : tm.Cfg) (stack : tm.K) :
    (currentStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).gateCount = 2 * space + 1 := by
  rw [currentStackIs, TransitionExpr.all_gateCount]
  have sumEq :
      (((List.finRange space).map fun position =>
        currentStackCellIs (tm := tm) (clockBits := clockBits) stack position
          (target.stk stack)[position.val]?).map
          TransitionExpr.gateCount).sum = space := by
    simpa [List.map_map, Function.comp_def] using
      (sum_map_constant (List.finRange space)
        (fun position =>
          (currentStackCellIs (tm := tm) (clockBits := clockBits) stack
            position (target.stk stack)[position.val]?).gateCount)
        1 (fun _ => rfl))
  rw [sumEq]
  simp
  omega

/-- A complete fixed current configuration test is affine in stack width. -/
@[simp]
theorem currentConfigIs_gateCount (target : tm.Cfg) :
    (currentConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).gateCount =
      Fintype.card tm.K * (2 * space + 2) + 5 := by
  classical
  rw [currentConfigIs]
  simp only [TransitionExpr.gateCount]
  rw [TransitionExpr.all_gateCount]
  have sumEq :
      (((finiteValues tm.K).map fun stack =>
        currentStackIs (tm := tm) (space := space)
          (clockBits := clockBits) target stack).map
          TransitionExpr.gateCount).sum =
        Fintype.card tm.K * (2 * space + 1) := by
    simpa [List.map_map, Function.comp_def] using
      (sum_map_constant (finiteValues tm.K)
        (fun stack =>
          (currentStackIs (tm := tm) (space := space)
            (clockBits := clockBits) target stack).gateCount)
        (2 * space + 1) (fun stack => currentStackIs_gateCount target stack))
  rw [sumEq]
  simp [currentLabelIs, currentControlIs, TransitionExpr.current,
    finiteValues_length]
  simp only [TransitionExpr.gateCount]
  ring

/-- All next-slice tests for one fixed stack have the same affine size. -/
@[simp]
theorem nextStackIs_gateCount (target : tm.Cfg) (stack : tm.K) :
    (nextStackIs (tm := tm) (space := space) (clockBits := clockBits)
      target stack).gateCount = 2 * space + 1 := by
  rw [nextStackIs, TransitionExpr.all_gateCount]
  have sumEq :
      (((List.finRange space).map fun position =>
        nextStackCellIs (tm := tm) (clockBits := clockBits) stack position
          (target.stk stack)[position.val]?).map
          TransitionExpr.gateCount).sum = space := by
    simpa [List.map_map, Function.comp_def] using
      (sum_map_constant (List.finRange space)
        (fun position =>
          (nextStackCellIs (tm := tm) (clockBits := clockBits) stack
            position (target.stk stack)[position.val]?).gateCount)
        1 (fun _ => rfl))
  rw [sumEq]
  simp
  omega

/-- A complete fixed next configuration test is affine in stack width. -/
@[simp]
theorem nextConfigIs_gateCount (target : tm.Cfg) :
    (nextConfigIs (tm := tm) (space := space) (clockBits := clockBits)
      target).gateCount =
      Fintype.card tm.K * (2 * space + 2) + 5 := by
  classical
  rw [nextConfigIs]
  simp only [TransitionExpr.gateCount]
  rw [TransitionExpr.all_gateCount]
  have sumEq :
      (((finiteValues tm.K).map fun stack =>
        nextStackIs (tm := tm) (space := space)
          (clockBits := clockBits) target stack).map
          TransitionExpr.gateCount).sum =
        Fintype.card tm.K * (2 * space + 1) := by
    simpa [List.map_map, Function.comp_def] using
      (sum_map_constant (finiteValues tm.K)
        (fun stack =>
          (nextStackIs (tm := tm) (space := space)
            (clockBits := clockBits) target stack).gateCount)
        (2 * space + 1) (fun stack => nextStackIs_gateCount target stack))
  rw [sumEq]
  simp [nextLabelIs, nextControlIs, TransitionExpr.next,
    finiteValues_length]
  simp only [TransitionExpr.gateCount]
  ring

/-- Resetting every next clock bit to zero is linear in clock width. -/
@[simp]
theorem clockReset_gateCount :
    (clockReset (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount = 3 * clockBits + 1 := by
  simp [clockReset, TransitionExpr.all_gateCount, clockAtoms_length,
    TransitionExpr.next, TransitionExpr.gateCount, Function.comp_def]
  omega

/-- The verified ripple-carry successor is quadratic in clock width. -/
theorem clockSuccessor_gateCount_le :
    (clockSuccessor (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount ≤
      12 * (clockBits + 1) ^ 2 := by
  unfold clockSuccessor
  simpa using TransitionExpr.binarySuccessor_gateCount_le
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits))
    (clockAtoms (tm := tm) (space := space) (clockBits := clockBits)) rfl

/-- The structural well-formedness portion is affine in represented stack
width, with a machine-dependent exact-one coefficient. -/
theorem wellFormedFields_gateCount_le :
    (wellFormedFields (tm := tm) (space := space)
      (clockBits := clockBits)).gateCount ≤
      (2 + Fintype.card tm.K * space) *
          (oneHotFieldNodeBudget (tm := tm) + 1) + 1 +
        (5 * (Fintype.card tm.K * space) + 1) + 1 := by
  unfold wellFormedFields
  simp only [TransitionExpr.gateCount]
  exact Nat.add_le_add_right
    (Nat.add_le_add oneHotFields_gateCount_le
      stackSuffixFields_gateCount_le) 1

/-- Closed machine-dependent budget for structural well-formedness. -/
def wellFormedNodeBudget : Nat :=
  (2 + Fintype.card tm.K * space) *
      (oneHotFieldNodeBudget (tm := tm) + 1) + 1 +
    (5 * (Fintype.card tm.K * space) + 1) + 1

/-- Exact node count shared by fixed current- and next-configuration tests. -/
def fixedConfigNodeCount : Nat :=
  Fintype.card tm.K * (2 * space + 2) + 5

/-- Every component of the designated reset relation except the fixed
machine's ordinary-step expression. -/
def designatedNonStepNodeBudget : Nat :=
  wellFormedNodeBudget (tm := tm) (space := space) +
    3 * fixedConfigNodeCount (tm := tm) (space := space) +
    (3 * clockBits + 1) + 12 * (clockBits + 1) ^ 2 + 7

/-- The full designated reset relation is polynomial in the explicit widths
once the fixed machine's symbolic statement expansion is bounded. -/
theorem designatedMachineResetClockExpression_gateCount_le
    (initial accepting : tm.Cfg) :
    (designatedMachineResetClockExpression (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).gateCount ≤
      designatedNonStepNodeBudget (tm := tm) (space := space)
        (clockBits := clockBits) +
      (machineStepExpression (tm := tm) (space := space)
        (clockBits := clockBits)).gateCount := by
  have wellFormedBound := wellFormedFields_gateCount_le
    (tm := tm) (space := space) (clockBits := clockBits)
  have successorBound := clockSuccessor_gateCount_le
    (tm := tm) (space := space) (clockBits := clockBits)
  simp only [designatedMachineResetClockExpression,
    designatedMachineResetExpression, designatedMachineOrdinaryExpression,
    designatedMachineAcceptsExpression, TransitionExpr.gateCount,
    currentConfigIs_gateCount, nextConfigIs_gateCount, clockReset_gateCount]
  unfold designatedNonStepNodeBudget wellFormedNodeBudget
    fixedConfigNodeCount
  omega

/-- Clause-count bound for the designated machine CNF.  The remaining
`machineStepExpression` term is handled by the finite-statement size proof. -/
theorem designatedMachinePeriodicCNF_clause_length_le
    (initial accepting : tm.Cfg) :
    (designatedMachinePeriodicCNF (tm := tm) (space := space)
      (clockBits := clockBits) initial accepting).clauses.length ≤
      3 * (designatedNonStepNodeBudget (tm := tm) (space := space)
          (clockBits := clockBits) +
        (machineStepExpression (tm := tm) (space := space)
          (clockBits := clockBits)).gateCount) + 1 := by
  unfold designatedMachinePeriodicCNF
  apply (requireTransitionExpr_clause_length_le _ _).trans
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 3
      (designatedMachineResetClockExpression_gateCount_le
        initial accepting)) 1

end BoundedMachineAtom

end PeriodicCNF

end LeanTrominoes
