import LeanTrominoes.FiniteStateCycleSearch
import Mathlib.Data.Fintype.Lattice

/-!
# Cyclic polynomial-space computations

The 1D PSPACE-hardness construction repeats a machine configuration at every
integer position.  A bounded clock advances at every ordinary transition, and
an accepting configuration resets both the clock and machine to the initial
configuration.  Consequently the local transition system has a directed
cycle exactly when the original deterministic computation accepts before the
clock expires.

This file proves that semantic core independently of any particular machine
encoding or CNF compilation.
-/

namespace LeanTrominoes

namespace PeriodicComputation

/-- A finite accepting computation with an explicit upper bound on its number
of transitions. -/
structure AcceptingTrace (Config : Type*) (initial : Config)
    (step : Config → Option Config) (accepts : Config → Prop)
    (limit : Nat) where
  length : Nat
  length_le : length ≤ limit
  states : Fin (length + 1) → Config
  starts : states 0 = initial
  accepts_last : accepts (states (Fin.last length))
  not_accepts : ∀ index : Fin length,
    ¬ accepts (states index.castSucc)
  steps : ∀ index : Fin length,
    step (states index.castSucc) = some (states index.succ)

/-- A machine configuration paired with the number of ordinary transitions
since the most recent accepting reset. -/
structure ResetClockState (Config : Type*) where
  clock : Nat
  config : Config

/-- The local reset relation used by the cyclic computation.  Accepting states
reset to clock zero and the initial configuration; all other states execute
one machine step and increment the clock without exceeding `limit`. -/
def ResetClockRelation {Config : Type*} (initial : Config)
    (step : Config → Option Config) (accepts : Config → Prop)
    (limit : Nat) :
    ResetClockState Config → ResetClockState Config → Prop :=
  fun current next =>
    current.clock ≤ limit ∧ next.clock ≤ limit ∧
      ((accepts current.config ∧
          next = ⟨0, initial⟩) ∨
        (¬ accepts current.config ∧ current.clock < limit ∧
          next.clock = current.clock + 1 ∧
          step current.config = some next.config))

private theorem fin_add_last_wraps {length : Nat}
    (index : Fin (Nat.succ length)) :
    index + 1 + Fin.last length = index := by
  have one_add_last :
      (1 : Fin (Nat.succ length)) + Fin.last length = 0 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.succ_eq_add_one, Nat.add_comm]
  rw [add_assoc, one_add_last, add_zero]

/-- An accepting trace closes into a directed reset cycle. -/
theorem hasCycle_of_acceptingTrace {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    (trace : AcceptingTrace Config initial step accepts limit) :
    FiniteState.HasCycle
      (ResetClockRelation initial step accepts limit) := by
  refine ⟨trace.length,
    fun index => (⟨index.val, trace.states index⟩ : ResetClockState Config), ?_⟩
  intro index
  change ResetClockRelation initial step accepts limit
    ⟨index.val, trace.states index⟩
    ⟨(index + 1).val, trace.states (index + 1)⟩
  have currentBound : index.val ≤ limit := by
    have traceBound := trace.length_le
    have := index.isLt
    omega
  have nextBound : (index + 1).val ≤ limit := by
    have traceBound := trace.length_le
    have := (index + 1).isLt
    omega
  refine ⟨currentBound, nextBound, ?_⟩
  by_cases beforeLast : index.val < trace.length
  · right
    have nextValue : (index + 1).val = index.val + 1 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : index.val + 1 < trace.length + 1)]
    have castSucc : index = (⟨index.val, beforeLast⟩ : Fin trace.length).castSucc :=
      Fin.ext rfl
    have successor : index + 1 = (⟨index.val, beforeLast⟩ : Fin trace.length).succ := by
      apply Fin.ext
      simp [nextValue]
    let traceIndex : Fin trace.length := ⟨index.val, beforeLast⟩
    refine ⟨?_, lt_of_lt_of_le beforeLast trace.length_le, nextValue, ?_⟩
    · intro accepted
      apply trace.not_accepts traceIndex
      rw [← castSucc]
      exact accepted
    · change step (trace.states index) = some (trace.states (index + 1))
      calc
        step (trace.states index) =
            step (trace.states traceIndex.castSucc) :=
          congrArg step (congrArg trace.states castSucc)
        _ = some (trace.states traceIndex.succ) := trace.steps traceIndex
        _ = some (trace.states (index + 1)) :=
          congrArg some (congrArg trace.states successor.symm)
  · left
    have atLast : index = Fin.last trace.length := by
      apply Fin.ext
      change index.val = trace.length
      have := index.isLt
      omega
    have nextZero : index + 1 = 0 := by
      apply Fin.ext
      simp [atLast]
    refine ⟨by simpa [atLast] using trace.accepts_last, ?_⟩
    simp [nextZero, trace.starts]

private theorem exists_accepting_index_of_cycleStep {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    {periodPred : Nat}
    {states : Fin (periodPred + 1) → ResetClockState Config}
    (cycleStep : ∀ index,
      ResetClockRelation initial step accepts limit
        (states index) (states (index + 1))) :
    ∃ index, accepts (states index).config := by
  by_contra noneAccept
  push Not at noneAccept
  obtain ⟨maximumIndex, maximal⟩ :=
    Finite.exists_max fun index : Fin (periodPred + 1) =>
      (states index).clock
  have edge := cycleStep maximumIndex
  rcases edge.2.2 with reset | ordinary
  · exact (noneAccept maximumIndex) reset.1
  · have increases :
        (states maximumIndex).clock <
          (states (maximumIndex + 1)).clock := by
      omega
    exact (not_lt_of_ge (maximal (maximumIndex + 1))) increases

/-- Every reset cycle contains an accepting state: otherwise its clock would
strictly increase around a finite cycle. -/
theorem exists_accepting_state_of_hasCycle {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    (cycle : FiniteState.HasCycle
      (ResetClockRelation initial step accepts limit)) :
    ∃ state : ResetClockState Config, accepts state.config := by
  obtain ⟨periodPred, states, cycleStep⟩ := cycle
  obtain ⟨index, accepted⟩ :=
    exists_accepting_index_of_cycleStep cycleStep
  exact ⟨states index, accepted⟩

/-- A reset cycle yields an accepting trace of the original transition
function. -/
theorem acceptingTrace_of_hasCycle {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    (cycle : FiniteState.HasCycle
      (ResetClockRelation initial step accepts limit)) :
    Nonempty (AcceptingTrace Config initial step accepts limit) := by
  classical
  obtain ⟨periodPred, cycleStates, cycleStep⟩ := cycle
  obtain ⟨acceptedIndex, acceptedAt⟩ :=
    exists_accepting_index_of_cycleStep cycleStep
  let start : Fin (periodPred + 1) := acceptedIndex + 1
  let segment : Nat → ResetClockState Config := fun length =>
    cycleStates (start + Fin.ofNat (periodPred + 1) length)
  have startState : segment 0 = ⟨0, initial⟩ := by
    have edge := cycleStep acceptedIndex
    rcases edge.2.2 with reset | ordinary
    · simpa [segment, start] using reset.2
    · exact (ordinary.1 acceptedAt).elim
  have wraps : segment periodPred = cycleStates acceptedIndex := by
    dsimp [segment, start]
    have castLast : Fin.ofNat (periodPred + 1) periodPred =
        Fin.last periodPred := by
      apply Fin.ext
      simp [Fin.ofNat]
    have wrapIndex : acceptedIndex + 1 +
        Fin.ofNat (periodPred + 1) periodPred = acceptedIndex := by
      rw [castLast]
      exact fin_add_last_wraps acceptedIndex
    exact congrArg cycleStates wrapIndex
  have acceptedPeriod : accepts (segment periodPred).config := by
    rw [wraps]
    exact acceptedAt
  have eventuallyAccepts : ∃ length, accepts (segment length).config :=
    ⟨periodPred, acceptedPeriod⟩
  let length := Nat.find eventuallyAccepts
  have acceptsLength : accepts (segment length).config :=
    Nat.find_spec eventuallyAccepts
  have beforeLength : ∀ index < length,
      ¬ accepts (segment index).config := by
    intro index indexLt acceptedIndex
    exact Nat.find_min eventuallyAccepts indexLt acceptedIndex
  have segmentStep (index : Nat) :
      ResetClockRelation initial step accepts limit
        (segment index) (segment (index + 1)) := by
    have edge := cycleStep
      (start + Fin.ofNat (periodPred + 1) index)
    have nextIndex : Fin.ofNat (periodPred + 1) (index + 1) =
        Fin.ofNat (periodPred + 1) index + 1 := by
      apply Fin.ext
      simp [Fin.ofNat, Fin.val_add, Nat.add_mod]
    simpa only [segment, nextIndex, ← add_assoc] using edge
  have clock_eq : ∀ index ≤ length, (segment index).clock = index := by
    intro index indexLe
    induction index with
    | zero => simp [startState]
    | succ index ih =>
        have indexLt : index < length := by omega
        have edge := segmentStep index
        rcases edge.2.2 with reset | ordinary
        · exact (beforeLength index indexLt reset.1).elim
        · rw [ordinary.2.2.1, ih (by omega)]
  have length_le_limit : length ≤ limit := by
    have sourceBound := (segmentStep length).1
    rw [clock_eq length (Nat.le_refl length)] at sourceBound
    exact sourceBound
  refine ⟨
    { length := length
      length_le := length_le_limit
      states := fun index => (segment index.val).config
      starts := by simp [startState]
      accepts_last := by simpa using acceptsLength
      not_accepts := ?_
      steps := ?_ }⟩
  · intro index
    exact beforeLength index.val index.isLt
  intro index
  have edge := segmentStep index.val
  rcases edge.2.2 with reset | ordinary
  · exact (beforeLength index.val index.isLt reset.1).elim
  · simpa using ordinary.2.2.2

private theorem exists_accepting_nat_of_biInfinitePath {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    {path : Int → ResetClockState Config}
    (follows : FiniteState.IsBiInfinitePath
      (ResetClockRelation initial step accepts limit) path)
    (start : Int) :
    ∃ index ≤ limit, accepts (path (start + index)).config := by
  by_contra noAcceptance
  push Not at noAcceptance
  have clock_eq : ∀ index ≤ limit + 1,
      (path (start + index)).clock = (path start).clock + index := by
    intro index indexLe
    induction index with
    | zero => simp
    | succ index ih =>
        have indexLeLimit : index ≤ limit := by omega
        have edge : ResetClockRelation initial step accepts limit
            (path (start + index)) (path (start + (index + 1))) := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
            follows (start + (index : Int))
        rcases edge.2.2 with reset | ordinary
        · exact (noAcceptance index indexLeLimit reset.1).elim
        · norm_num only [Nat.cast_add, Nat.cast_one]
          rw [ordinary.2.2.1, ih (by omega)]
          omega
  have finalEdge : ResetClockRelation initial step accepts limit
      (path (start + limit)) (path (start + (limit + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      follows (start + (limit : Int))
  have nextBound := finalEdge.2.1
  have finalClock := clock_eq (limit + 1) (by omega)
  norm_num only [Nat.cast_add, Nat.cast_one] at finalClock
  rw [finalClock] at nextBound
  omega

/-- Every bi-infinite reset-clock path contains a bounded accepting trace.
The clock bound supplies the well-foundedness; the configuration type itself
need not be finite. -/
theorem acceptingTrace_of_hasBiInfinitePath {Config : Type*}
    {initial : Config} {step : Config → Option Config}
    {accepts : Config → Prop} {limit : Nat}
    (infinite : FiniteState.HasBiInfinitePath
      (ResetClockRelation initial step accepts limit)) :
    Nonempty (AcceptingTrace Config initial step accepts limit) := by
  classical
  obtain ⟨path, follows⟩ := infinite
  obtain ⟨acceptedIndex, _, acceptedAt⟩ :=
    exists_accepting_nat_of_biInfinitePath follows 0
  let start : Int := acceptedIndex + 1
  let segment : Nat → ResetClockState Config := fun index =>
    path (start + index)
  have startState : segment 0 = ⟨0, initial⟩ := by
    have edge := follows (acceptedIndex : Int)
    rcases edge.2.2 with reset | ordinary
    · simpa [segment, start] using reset.2
    · exact (ordinary.1 (by simpa using acceptedAt)).elim
  obtain ⟨acceptedLength, acceptedLengthLe, acceptsLength⟩ :=
    exists_accepting_nat_of_biInfinitePath follows start
  have eventuallyAccepts : ∃ length,
      length ≤ limit ∧ accepts (segment length).config :=
    ⟨acceptedLength, acceptedLengthLe, acceptsLength⟩
  let length := Nat.find eventuallyAccepts
  have lengthSpec : length ≤ limit ∧ accepts (segment length).config :=
    Nat.find_spec eventuallyAccepts
  have beforeLength : ∀ index < length,
      ¬ accepts (segment index).config := by
    intro index indexLt accepted
    exact Nat.find_min eventuallyAccepts indexLt
      ⟨by omega, accepted⟩
  have segmentStep (index : Nat) :
      ResetClockRelation initial step accepts limit
        (segment index) (segment (index + 1)) := by
    simpa only [segment, Nat.cast_add, Nat.cast_one, add_assoc] using
      follows (start + (index : Int))
  refine ⟨
    { length := length
      length_le := lengthSpec.1
      states := fun index => (segment index.val).config
      starts := by simp [startState]
      accepts_last := by simpa using lengthSpec.2
      not_accepts := ?_
      steps := ?_ }⟩
  · intro index
    exact beforeLength index.val index.isLt
  · intro index
    have edge := segmentStep index.val
    rcases edge.2.2 with reset | ordinary
    · exact (beforeLength index.val index.isLt reset.1).elim
    · simpa using ordinary.2.2.2

/-- The cyclic reset system characterizes bounded acceptance. -/
theorem hasCycle_iff_acceptingTrace {Config : Type*}
    (initial : Config) (step : Config → Option Config)
    (accepts : Config → Prop) (limit : Nat) :
    FiniteState.HasCycle (ResetClockRelation initial step accepts limit) ↔
      Nonempty (AcceptingTrace Config initial step accepts limit) := by
  constructor
  · exact acceptingTrace_of_hasCycle
  · rintro ⟨trace⟩
    exact hasCycle_of_acceptingTrace trace

end PeriodicComputation

end LeanTrominoes
