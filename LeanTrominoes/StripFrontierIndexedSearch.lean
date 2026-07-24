import LeanTrominoes.IndexedSavitch
import LeanTrominoes.StripFrontierIndex
import LeanTrominoes.StripFrontierReconstruction

/-!
# Enumeration-free indexed search for strip frontiers

This file instantiates the arithmetic Savitch search with sparse tromino
frontiers.  A bounded index is decoded to one semantic `WindowState`, the
ordinary transition predicate is checked there, and the state is discarded
before the next midpoint is tried.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

/-- Semantic state decoded from a bounded arithmetic index. -/
def semanticOfIndex (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Fin (indexCount periodicStrip)) :
    WindowState periodicStrip :=
  let raw := ofIndex periodicStrip stateIndex.val
  let valid := ofIndex_isValid periodPositive stateIndex.isLt
  { phase := ⟨raw.phase, valid.1⟩
    assignment := raw.assignmentAt periodicStrip }

theorem decode_ofIndex_eq_some (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Fin (indexCount periodicStrip)) :
    decode periodicStrip (ofIndex periodicStrip stateIndex.val) =
      some (semanticOfIndex periodicStrip periodPositive stateIndex) := by
  rw [decode, dif_pos
    (ofIndex_isValid periodPositive stateIndex.isLt)]
  rfl

/-- Arithmetic index of a semantic frontier state. -/
def indexOfWindow {periodicStrip : PeriodicStrip}
    (state : WindowState periodicStrip) :
    Fin (indexCount periodicStrip) :=
  ⟨index periodicStrip (encode state),
    index_lt_indexCount (encode_isValid state)⟩

@[simp]
theorem semanticOfIndex_indexOfWindow {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (state : WindowState periodicStrip) :
    semanticOfIndex periodicStrip periodPositive (indexOfWindow state) =
      state := by
  have decoded :=
    decode_ofIndex_eq_some periodicStrip periodPositive
      (indexOfWindow state)
  change
    decode periodicStrip
        (ofIndex periodicStrip (index periodicStrip (encode state))) =
      some (semanticOfIndex periodicStrip periodPositive
        (indexOfWindow state)) at decoded
  rw [ofIndex_index (encode_isValid state), decode_encode] at decoded
  exact Option.some.inj decoded.symm

/-- Boolean transition check on natural indices.  Out-of-range indices are
rejected before decoding. -/
def indexedTransitionBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (first last : Nat) : Bool :=
  if firstBound : first < indexCount periodicStrip then
    if lastBound : last < indexCount periodicStrip then
      decide (WindowState.Transition tromino
        (semanticOfIndex periodicStrip periodPositive
          ⟨first, firstBound⟩)
        (semanticOfIndex periodicStrip periodPositive
          ⟨last, lastBound⟩))
    else
      false
  else
    false

theorem indexedRelation_iff_transition (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (first last : Fin (indexCount periodicStrip)) :
    FiniteState.IndexedRelation (indexCount periodicStrip)
        (indexedTransitionBool tromino periodicStrip periodPositive)
        first last ↔
      WindowState.Transition tromino
        (semanticOfIndex periodicStrip periodPositive first)
        (semanticOfIndex periodicStrip periodPositive last) := by
  simp [FiniteState.IndexedRelation, indexedTransitionBool,
    decide_eq_true_eq]

theorem indexed_hasCycle_iff_hasCycle (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period) :
    FiniteState.HasCycle
        (FiniteState.IndexedRelation (indexCount periodicStrip)
          (indexedTransitionBool tromino periodicStrip periodPositive)) ↔
      FiniteState.HasCycle
        (WindowState.Transition tromino :
          WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  constructor
  · rintro ⟨periodPred, states, step⟩
    refine ⟨periodPred,
      fun index =>
        semanticOfIndex periodicStrip periodPositive (states index), ?_⟩
    intro index
    exact (indexedRelation_iff_transition tromino periodicStrip
      periodPositive _ _).mp (step index)
  · rintro ⟨periodPred, states, step⟩
    refine ⟨periodPred, fun index => indexOfWindow (states index), ?_⟩
    intro index
    apply (indexedRelation_iff_transition tromino periodicStrip
      periodPositive _ _).mpr
    simpa using step index

/-- Enumeration-free sparse-frontier decision procedure. -/
def periodicStripTrominoTilingIndexBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Bool :=
  if wellFormed : periodicStrip.IsWellFormed then
    FiniteState.cycleSearchIndexBool (indexCount periodicStrip)
      (indexedTransitionBool tromino periodicStrip wellFormed.2.1)
  else
    false

theorem periodicStripTrominoTilingIndexBool_eq_true_iff
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    periodicStripTrominoTilingIndexBool tromino periodicStrip = true ↔
      PeriodicStripTrominoTiling tromino periodicStrip := by
  by_cases wellFormed : periodicStrip.IsWellFormed
  · rw [periodicStripTrominoTilingIndexBool, dif_pos wellFormed,
      FiniteState.cycleSearchIndexBool_eq_true_iff,
      indexed_hasCycle_iff_hasCycle tromino periodicStrip wellFormed.2.1,
      ← WindowState.tileable_iff_hasCycle tromino wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]
  · rw [periodicStripTrominoTilingIndexBool, dif_neg wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]

end RawWindowState
end PeriodicStrip
end LeanTrominoes
