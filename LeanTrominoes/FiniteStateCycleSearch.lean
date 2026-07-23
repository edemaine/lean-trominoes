import LeanTrominoes.FiniteStateReachability

/-!
# Polynomial-space finite-state cycle search

This file reduces directed-cycle existence to a single edge followed by the
logarithmic-depth reachability recurrence.  It proves the executable Boolean
search correct by translating exact walks to and from cyclic state sequences.
-/

namespace LeanTrominoes.FiniteState

open Fin.NatCast

/-- Existence of indexed vertices of a directed walk, including both
endpoints. -/
def HasWalkData {α : Type*} (relation : α → α → Prop)
    (length : Nat) (first last : α) : Prop :=
  ∃ states : Fin (length + 1) → α,
    states 0 = first ∧
      states (Fin.last length) = last ∧
        ∀ index : Fin length,
          relation (states index.castSucc) (states index.succ)

namespace ReachIn

/-- Recover explicit indexed vertices from an inductive exact-length walk. -/
theorem hasWalkData {α : Type*} {relation : α → α → Prop}
    {length : Nat} {first last : α}
    (walk : ReachIn relation length first last) :
    HasWalkData relation length first last := by
  induction walk with
  | refl state =>
      exact ⟨fun _ => state, rfl, rfl, fun index => Fin.elim0 index⟩
  | @tail length first middle last previous edge ih =>
      obtain ⟨previousStates, previousStart, previousFinish,
        previousStep⟩ := ih
      let states : Fin (length + 1 + 1) → α := fun index =>
        if beforeLast : index.val < length + 1 then
          previousStates ⟨index.val, beforeLast⟩
        else
          last
      refine ⟨states, ?_, ?_, ?_⟩
      · simp [states, previousStart]
      · simp [states]
      · intro index
        unfold states
        have currentBefore : index.castSucc.val < length + 1 := index.isLt
        rw [dif_pos currentBefore]
        by_cases nextBefore : index.val + 1 < length + 1
        · have nextBefore' : index.succ.val < length + 1 := nextBefore
          rw [dif_pos nextBefore']
          let previousIndex : Fin length := ⟨index.val, by omega⟩
          have currentIndex :
              (⟨index.castSucc.val, currentBefore⟩ : Fin (length + 1)) =
                previousIndex.castSucc := by
            apply Fin.ext
            rfl
          have nextIndex :
              (⟨index.succ.val, nextBefore'⟩ : Fin (length + 1)) =
                previousIndex.succ := by
            apply Fin.ext
            rfl
          rw [currentIndex, nextIndex]
          exact previousStep previousIndex
        · have nextNotBefore : ¬index.succ.val < length + 1 := nextBefore
          rw [dif_neg nextNotBefore]
          have atLast : index.val = length := by omega
          have currentIndex :
              (⟨index.castSucc.val, currentBefore⟩ : Fin (length + 1)) =
                Fin.last length := by
            apply Fin.ext
            exact atLast
          rw [currentIndex, previousFinish]
          exact edge

end ReachIn

/-- A positive closed walk contains a directed cycle. -/
theorem hasCycle_of_closed_reachIn {α : Type*}
    {relation : α → α → Prop} {length : Nat} {state : α}
    (positive : 0 < length)
    (walk : ReachIn relation length state state) :
    HasCycle relation := by
  obtain ⟨walkStates, walkStart, walkFinish, walkStep⟩ :=
    walk.hasWalkData
  have cycleSize : (length - 1) + 1 = length := by omega
  let cycleStates : Fin ((length - 1) + 1) → α :=
    fun index => walkStates ⟨index.val, by omega⟩
  refine ⟨length - 1, cycleStates, ?_⟩
  intro index
  have nextLtLength : (index + 1).val < length := calc
    (index + 1).val < (length - 1) + 1 := (index + 1).isLt
    _ = length := cycleSize
  have nextBound : (index + 1).val < length + 1 :=
    Nat.lt_succ_of_lt nextLtLength
  change relation
    (walkStates ⟨index.val, by omega⟩)
    (walkStates ⟨(index + 1).val, nextBound⟩)
  by_cases beforeEnd : index.val + 1 < length
  · have nextValue : (index + 1).val = index.val + 1 := by
      simp [Fin.val_add, cycleSize, Nat.mod_eq_of_lt beforeEnd]
    have nextIndex :
        (⟨(index + 1).val, nextBound⟩ : Fin (length + 1)) =
          ⟨index.val + 1, by omega⟩ := by
      apply Fin.ext
      exact nextValue
    rw [nextIndex]
    let walkIndex : Fin length := ⟨index.val, by omega⟩
    have edge := walkStep walkIndex
    convert edge using 1
    · apply congrArg walkStates
      apply Fin.ext
      rfl
    · apply congrArg walkStates
      apply Fin.ext
      rfl
  · have atEnd : index.val + 1 = length := by
      have indexBound : index.val < length := by
        simpa only [cycleSize] using index.isLt
      omega
    have nextValue : (index + 1).val = 0 := by
      simp [Fin.val_add, cycleSize, atEnd]
    have nextIndex :
        (⟨(index + 1).val, nextBound⟩ : Fin (length + 1)) =
          (0 : Fin (length + 1)) := by
      apply Fin.ext
      exact nextValue
    rw [nextIndex]
    let walkIndex : Fin length := ⟨index.val, by omega⟩
    have edge := walkStep walkIndex
    have walkIndexLast : walkIndex.succ = Fin.last length := by
      apply Fin.ext
      exact atEnd
    rw [walkIndexLast, walkFinish, ← walkStart] at edge
    convert edge using 1
    · apply congrArg walkStates
      apply Fin.ext
      rfl

/-- Following a cyclic state sequence for any number of steps produces an
exact directed walk. -/
theorem reachIn_cycleSegment {α : Type*} {relation : α → α → Prop}
    {periodPred : Nat} {states : Fin (periodPred + 1) → α}
    (step : ∀ index, relation (states index) (states (index + 1)))
    (start : Fin (periodPred + 1)) (length : Nat) :
    ReachIn relation length (states start)
      (states (start + (↑length : Fin (periodPred + 1)))) := by
  induction length with
  | zero =>
      simpa using ReachIn.refl (relation := relation) (states start)
  | succ length ih =>
      have extended :=
        ReachIn.tail ih
          (step (start + (↑length : Fin (periodPred + 1))))
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using extended

/-- Deterministic cycle search using one edge followed by logarithmic-depth
Savitch reachability back to its source. -/
def cycleSearchBool {α : Type*} [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation] : Bool :=
  decide (∃ first second,
    relation first second ∧
      divideReachBool relation (savitchDepth α) second first = true)

theorem cycleSearchBool_eq_true_iff {α : Type*}
    [Fintype α] [DecidableEq α]
    (relation : α → α → Prop) [DecidableRel relation] :
    cycleSearchBool relation = true ↔ HasCycle relation := by
  unfold cycleSearchBool
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨first, second, edge, returns⟩
    obtain ⟨returnLength, -, returnWalk⟩ :=
      (divideReachBool_savitchDepth_eq_true_iff
        relation second first).mp returns
    have outgoing :
        ReachIn relation 1 first second :=
      ReachIn.tail (ReachIn.refl first) edge
    apply hasCycle_of_closed_reachIn (length := 1 + returnLength)
      (by omega)
    exact outgoing.trans returnWalk
  · intro cycle
    obtain ⟨periodPred, states, step⟩ :=
      (hasCycle_iff_hasBoundedCycle relation).mp cycle
    let first := states 0
    let second := states (0 + 1)
    refine ⟨first, second, step 0, ?_⟩
    apply (divideReachBool_savitchDepth_eq_true_iff
      relation second first).mpr
    refine ⟨periodPred.val, ?_, ?_⟩
    · exact (Nat.lt_of_lt_of_le periodPred.isLt
        (card_le_pow_savitchDepth α)).le
    · have segment :=
        reachIn_cycleSegment step (0 + 1) periodPred.val
      have wraps :
          (0 + 1 : Fin (periodPred.val + 1)) +
              (↑periodPred.val : Fin (periodPred.val + 1)) = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_natCast, Fin.val_zero]
        simp [Nat.add_comm]
      rw [wraps] at segment
      simpa [first, second] using segment

end LeanTrominoes.FiniteState
