import LeanTrominoes.FiniteStateCycleSearch

/-!
# Savitch search over arithmetic state indices

The generic finite-state search quantifies over a `Fintype`, which is ideal
for semantic correctness but can hide construction of a full state
enumeration.  This file implements the same search over natural indices below
an explicit bound.  Bounded existential search is a primitive recursion over
the bound and never constructs `List.range bound`.
-/

namespace LeanTrominoes.FiniteState

open Fin.NatCast

/-- Does `predicate` hold at some natural index below `bound`?

This is intentionally a direct primitive recursion rather than
`(List.range bound).any predicate`: the latter first allocates the whole
range. -/
def boundedAny (predicate : Nat → Bool) : Nat → Bool
  | 0 => false
  | bound + 1 => predicate bound || boundedAny predicate bound

theorem boundedAny_eq_true_iff (predicate : Nat → Bool) (bound : Nat) :
    boundedAny predicate bound = true ↔
      ∃ index < bound, predicate index = true := by
  induction bound with
  | zero => simp [boundedAny]
  | succ bound induction =>
      rw [boundedAny, Bool.or_eq_true, induction]
      constructor
      · rintro (atLast | ⟨index, indexBelow, succeeds⟩)
        · exact ⟨bound, by omega, atLast⟩
        · exact ⟨index, by omega, succeeds⟩
      · rintro ⟨index, indexBelow, succeeds⟩
        by_cases atLast : index = bound
        · left
          simpa [atLast] using succeeds
        · right
          exact ⟨index, by omega, succeeds⟩

/-- The relation on the finite index type induced by a Boolean relation on
naturals. -/
def IndexedRelation (stateCount : Nat)
    (relation : Nat → Nat → Bool) :
    Fin stateCount → Fin stateCount → Prop :=
  fun first last => relation first.val last.val = true

instance (stateCount : Nat) (relation : Nat → Nat → Bool) :
    DecidableRel (IndexedRelation stateCount relation) := by
  intro first last
  exact decidable_of_iff
    (relation first.val last.val = true) Iff.rfl

/-- Savitch's reachability recurrence, enumerating midpoint indices directly
below `stateCount`. -/
def divideReachIndexBool (stateCount : Nat)
    (relation : Nat → Nat → Bool) :
    Nat → Nat → Nat → Bool
  | 0, first, last => decide (first = last) || relation first last
  | depth + 1, first, last =>
      boundedAny (fun middle =>
        divideReachIndexBool stateCount relation depth first middle &&
          divideReachIndexBool stateCount relation depth middle last)
        stateCount

theorem divideReachIndexBool_eq_true_iff
    (stateCount : Nat) (relation : Nat → Nat → Bool)
    (depth first last : Nat)
    (firstBound : first < stateCount) (lastBound : last < stateCount) :
    divideReachIndexBool stateCount relation depth first last = true ↔
      DivideReach (IndexedRelation stateCount relation) depth
        ⟨first, firstBound⟩ ⟨last, lastBound⟩ := by
  induction depth generalizing first last with
  | zero =>
      simp [divideReachIndexBool, DivideReach, IndexedRelation, Fin.ext_iff]
  | succ depth induction =>
      rw [divideReachIndexBool, boundedAny_eq_true_iff]
      constructor
      · rintro ⟨middle, middleBound, succeeds⟩
        rw [Bool.and_eq_true] at succeeds
        obtain ⟨firstHalf, secondHalf⟩ := succeeds
        exact ⟨⟨middle, middleBound⟩,
          (induction first middle firstBound middleBound).mp firstHalf,
          (induction middle last middleBound lastBound).mp secondHalf⟩
      · rintro ⟨middle, firstHalf, secondHalf⟩
        refine ⟨middle.val, middle.isLt, ?_⟩
        rw [Bool.and_eq_true]
        exact
          ⟨(induction first middle.val firstBound middle.isLt).mpr
              firstHalf,
            (induction middle.val last middle.isLt lastBound).mpr
              secondHalf⟩

/-- The logarithmic recursion depth used for a graph with `stateCount`
arithmetically indexed vertices. -/
def indexSavitchDepth (stateCount : Nat) : Nat :=
  (Nat.log 2 stateCount).succ

theorem indexSavitchDepth_eq_fin (stateCount : Nat) :
    indexSavitchDepth stateCount = savitchDepth (Fin stateCount) := by
  simp [indexSavitchDepth, savitchDepth]

/-- Directed-cycle search over arithmetic indices at an explicit Savitch
recursion depth. -/
def cycleSearchIndexBoolAtDepth (stateCount depth : Nat)
    (relation : Nat → Nat → Bool) : Bool :=
  boundedAny (fun first =>
    boundedAny (fun second =>
      relation first second &&
        divideReachIndexBool stateCount relation
          depth second first)
      stateCount)
    stateCount

theorem cycleSearchIndexBoolAtDepth_eq_true_iff
    (stateCount depth : Nat) (relation : Nat → Nat → Bool)
    (depthSufficient : stateCount ≤ 2 ^ depth) :
    cycleSearchIndexBoolAtDepth stateCount depth relation = true ↔
      HasCycle (IndexedRelation stateCount relation) := by
  rw [cycleSearchIndexBoolAtDepth, boundedAny_eq_true_iff]
  constructor
  · rintro ⟨first, firstBound, secondSearch⟩
    rw [boundedAny_eq_true_iff] at secondSearch
    obtain ⟨second, secondBound, succeeds⟩ := secondSearch
    rw [Bool.and_eq_true] at succeeds
    obtain ⟨edge, returns⟩ := succeeds
    have returnDivide :=
      (divideReachIndexBool_eq_true_iff
      stateCount relation depth
      second first secondBound firstBound).mp returns
    have returnReach :
        ReachWithin (IndexedRelation stateCount relation)
          (2 ^ depth)
          ⟨second, secondBound⟩ ⟨first, firstBound⟩ :=
      (divideReach_iff_reachWithin_pow
        (IndexedRelation stateCount relation)
        depth _ _).mp returnDivide
    obtain ⟨returnLength, -, returnWalk⟩ := returnReach
    have outgoing :
        ReachIn (IndexedRelation stateCount relation) 1
          ⟨first, firstBound⟩ ⟨second, secondBound⟩ :=
      ReachIn.tail (ReachIn.refl _) edge
    apply hasCycle_of_closed_reachIn (length := 1 + returnLength)
      (by omega)
    exact outgoing.trans returnWalk
  · intro cycle
    obtain ⟨periodPred, states, step⟩ :=
      (hasCycle_iff_hasBoundedCycle
        (IndexedRelation stateCount relation)).mp cycle
    let first := states 0
    let second := states (0 + 1)
    refine ⟨first.val, first.isLt, ?_⟩
    rw [boundedAny_eq_true_iff]
    refine ⟨second.val, second.isLt, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨step 0, ?_⟩
    apply (divideReachIndexBool_eq_true_iff
      stateCount relation depth
      second.val first.val second.isLt first.isLt).mpr
    apply (divideReach_iff_reachWithin_pow
      (IndexedRelation stateCount relation)
      depth second first).mpr
    refine ⟨periodPred.val, ?_, ?_⟩
    · have periodBound :
          periodPred.val < Fintype.card (Fin stateCount) :=
        periodPred.isLt
      simpa using
        (periodBound.trans_le (by simpa using depthSufficient)).le
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

/-- Enlarging the ambient finite index type does not create or destroy
cycles when every true edge remains supported on the original prefix. -/
theorem hasCycle_indexedRelation_pad
    (small large : Nat) (relation : Nat → Nat → Bool)
    (smallLe : small ≤ large)
    (supported :
      ∀ first last,
        relation first last = true →
          first < small ∧ last < small) :
    HasCycle (IndexedRelation large relation) ↔
      HasCycle (IndexedRelation small relation) := by
  constructor
  · rintro ⟨periodPred, states, step⟩
    have stateBound :
        ∀ index, (states index).val < small := by
      intro index
      have edge := step index
      exact (supported _ _ edge).1
    refine ⟨periodPred,
      fun index => ⟨(states index).val, stateBound index⟩, ?_⟩
    intro index
    exact step index
  · rintro ⟨periodPred, states, step⟩
    refine ⟨periodPred,
      fun index =>
        ⟨(states index).val,
          (states index).isLt.trans_le smallLe⟩, ?_⟩
    intro index
    exact step index

/-- Cycle search may use any sufficiently large padded state bound, provided
the Boolean edge relation is supported on the original prefix. -/
theorem cycleSearchIndexBoolAtDepth_pad_eq_true_iff
    (small large depth : Nat) (relation : Nat → Nat → Bool)
    (largeDepth : large ≤ 2 ^ depth)
    (smallLe : small ≤ large)
    (supported :
      ∀ first last,
        relation first last = true →
          first < small ∧ last < small) :
    cycleSearchIndexBoolAtDepth large depth relation = true ↔
      HasCycle (IndexedRelation small relation) := by
  rw [cycleSearchIndexBoolAtDepth_eq_true_iff
    large depth relation largeDepth]
  exact hasCycle_indexedRelation_pad
    small large relation smallLe supported

/-- Directed-cycle search at the canonical logarithmic depth. -/
def cycleSearchIndexBool (stateCount : Nat)
    (relation : Nat → Nat → Bool) : Bool :=
  cycleSearchIndexBoolAtDepth stateCount
    (indexSavitchDepth stateCount) relation

theorem cycleSearchIndexBool_eq_true_iff
    (stateCount : Nat) (relation : Nat → Nat → Bool) :
    cycleSearchIndexBool stateCount relation = true ↔
      HasCycle (IndexedRelation stateCount relation) := by
  apply cycleSearchIndexBoolAtDepth_eq_true_iff
  rw [indexSavitchDepth_eq_fin]
  simpa using card_le_pow_savitchDepth (Fin stateCount)

end LeanTrominoes.FiniteState
