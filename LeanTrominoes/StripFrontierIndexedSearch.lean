import LeanTrominoes.IndexedSavitch
import LeanTrominoes.EncodingBounds
import LeanTrominoes.StripFrontierIndex
import LeanTrominoes.StripFrontierReconstruction
import LeanTrominoes.StripFrontierRawTransition

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
  raw.toWindowState periodicStrip valid

theorem decode_ofIndex_eq_some (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Fin (indexCount periodicStrip)) :
    decode periodicStrip (ofIndex periodicStrip stateIndex.val) =
      some (semanticOfIndex periodicStrip periodPositive stateIndex) := by
  unfold decode semanticOfIndex
  rw [dif_pos (ofIndex_isValid periodPositive stateIndex.isLt)]

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

/-- Proof-free Boolean transition check on natural indices.  Out-of-range
indices are rejected before decoding. -/
def indexedTransitionRawBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Bool :=
  if _firstBound : first < indexCount periodicStrip then
    if _lastBound : last < indexCount periodicStrip then
      (ofIndex periodicStrip first).transitionBool tromino periodicStrip
        (ofIndex periodicStrip last)
    else
      false
  else
    false

/-- Indexed transition with the positivity witness expected by the semantic
correctness interface.  The executable raw test does not inspect the proof. -/
def indexedTransitionBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (_periodPositive : 0 < periodicStrip.period)
    (first last : Nat) : Bool :=
  indexedTransitionRawBool tromino periodicStrip first last

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
  rw [FiniteState.IndexedRelation, indexedTransitionBool,
    indexedTransitionRawBool,
    dif_pos first.isLt, dif_pos last.isLt,
    transitionBool_eq_true_iff,
    transition_iff_toWindowState tromino periodicStrip
      (ofIndex periodicStrip first.val) (ofIndex periodicStrip last.val)
      (ofIndex_isValid periodPositive first.isLt)
      (ofIndex_isValid periodPositive last.isLt)]
  rfl

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

theorem indexCount_eq_windowState_card (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip =
      Fintype.card (WindowState periodicStrip) := by
  rw [indexCount_eq, WindowState.windowState_card]

/-- A primitive-recursion-friendly sufficient Savitch depth, linear in the
actual binary input encoding length. -/
def stripSearchDepth (periodicStrip : PeriodicStrip) : Nat :=
  21 * ((Complexity.primcodableFinEncoding PeriodicStrip).encode
    periodicStrip).length + 1

theorem indexCount_le_pow_stripSearchDepth
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤ 2 ^ stripSearchDepth periodicStrip := by
  rw [indexCount_eq_windowState_card]
  exact (FiniteState.card_le_pow_savitchDepth
    (WindowState periodicStrip)).trans
      (Nat.pow_le_pow_right (by omega)
        (WindowState.savitchDepth_le_encoding_length periodicStrip))

/-- Enumeration-free sparse-frontier decision procedure. -/
def periodicStripTrominoTilingIndexBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Bool :=
  if wellFormed : periodicStrip.IsWellFormed then
    FiniteState.cycleSearchIndexBoolAtDepth (indexCount periodicStrip)
      (stripSearchDepth periodicStrip)
      (indexedTransitionBool tromino periodicStrip wellFormed.2.1)
  else
    false

theorem periodicStripTrominoTilingIndexBool_eq_true_iff
    (tromino : Tromino) (periodicStrip : PeriodicStrip) :
    periodicStripTrominoTilingIndexBool tromino periodicStrip = true ↔
      PeriodicStripTrominoTiling tromino periodicStrip := by
  by_cases wellFormed : periodicStrip.IsWellFormed
  · rw [periodicStripTrominoTilingIndexBool, dif_pos wellFormed,
      FiniteState.cycleSearchIndexBoolAtDepth_eq_true_iff
        _ _ _ (indexCount_le_pow_stripSearchDepth periodicStrip),
      indexed_hasCycle_iff_hasCycle tromino periodicStrip wellFormed.2.1,
      ← WindowState.tileable_iff_hasCycle tromino wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]
  · rw [periodicStripTrominoTilingIndexBool, dif_neg wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]

end RawWindowState
end PeriodicStrip
end LeanTrominoes
