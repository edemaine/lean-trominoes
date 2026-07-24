import LeanTrominoes.IndexedSavitchDFSCorrectness
import LeanTrominoes.EncodingBounds
import LeanTrominoes.StripFrontierIndex
import LeanTrominoes.StripFrontierReconstruction
import LeanTrominoes.StripFrontierRawTransition

/-!
# Enumeration-free indexed search for strip frontiers

This file instantiates the arithmetic Savitch search with sparse tromino
frontiers.  Every ambient index is decoded modulo the period and into one
fixed-length base-nine word, then projected to a semantic `WindowState`.
Canonical indices embed every semantic state, while noncanonical padded
indices merely add redundant representatives.
-/

namespace LeanTrominoes
namespace PeriodicStrip
namespace RawWindowState

/-- Semantic state decoded from any natural index. -/
def semanticOfNat (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Nat) :
    WindowState periodicStrip :=
  (ofIndex periodicStrip stateIndex).toWindowState periodicStrip
    (ofIndex_isValid_of_periodPositive periodPositive stateIndex)

/-- Semantic state decoded from a canonical bounded arithmetic index. -/
def semanticOfIndex (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Fin (indexCount periodicStrip)) :
    WindowState periodicStrip :=
  semanticOfNat periodicStrip periodPositive stateIndex.val

theorem decode_ofIndex_eq_some (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateIndex : Fin (indexCount periodicStrip)) :
    decode periodicStrip (ofIndex periodicStrip stateIndex.val) =
      some (semanticOfIndex periodicStrip periodPositive stateIndex) := by
  unfold decode semanticOfIndex semanticOfNat
  rw [dif_pos
    (ofIndex_isValid_of_periodPositive periodPositive stateIndex.val)]

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

@[simp]
theorem semanticOfNat_indexOfWindow {periodicStrip : PeriodicStrip}
    (periodPositive : 0 < periodicStrip.period)
    (state : WindowState periodicStrip) :
    semanticOfNat periodicStrip periodPositive
        (indexOfWindow state).val =
      state := by
  exact semanticOfIndex_indexOfWindow periodPositive state

/-- Proof-free Boolean transition check on natural indices.  Every index is
decoded to a valid fixed-length raw state; padded indices therefore produce
redundant semantic representatives instead of requiring an exact range
check. -/
def indexedTransitionRawBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Bool :=
  (ofIndex periodicStrip first).transitionBool tromino periodicStrip
    (ofIndex periodicStrip last)

/-- Indexed transition with the positivity witness expected by the semantic
correctness interface.  The executable raw test does not inspect the proof. -/
def indexedTransitionBool (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (_periodPositive : 0 < periodicStrip.period)
    (first last : Nat) : Bool :=
  indexedTransitionRawBool tromino periodicStrip first last

theorem indexedTransitionRawBool_eq_true_iff_transition
    (tromino : Tromino) (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (first last : Nat) :
    indexedTransitionRawBool tromino periodicStrip first last = true ↔
      WindowState.Transition tromino
        (semanticOfNat periodicStrip periodPositive first)
        (semanticOfNat periodicStrip periodPositive last) := by
  rw [indexedTransitionRawBool, transitionBool_eq_true_iff,
    transition_iff_toWindowState tromino periodicStrip
      (ofIndex periodicStrip first) (ofIndex periodicStrip last)
      (ofIndex_isValid_of_periodPositive periodPositive first)
      (ofIndex_isValid_of_periodPositive periodPositive last)]
  rfl

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
  exact indexedTransitionRawBool_eq_true_iff_transition
    tromino periodicStrip periodPositive first.val last.val

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

/-- Enlarging the ambient index range only adds representatives that project
to existing semantic states.  Conversely, canonical indices embed every
semantic state below any bound containing `indexCount`. -/
theorem paddedIndexed_hasCycle_iff_hasCycle (tromino : Tromino)
    (periodicStrip : PeriodicStrip)
    (periodPositive : 0 < periodicStrip.period)
    (stateBound : Nat)
    (canonicalFits : indexCount periodicStrip ≤ stateBound) :
    FiniteState.HasCycle
        (FiniteState.IndexedRelation stateBound
          (indexedTransitionBool tromino periodicStrip periodPositive)) ↔
      FiniteState.HasCycle
        (WindowState.Transition tromino :
          WindowState periodicStrip → WindowState periodicStrip → Prop) := by
  constructor
  · rintro ⟨periodPred, states, step⟩
    refine ⟨periodPred,
      fun index =>
        semanticOfNat periodicStrip periodPositive (states index).val,
      ?_⟩
    intro index
    exact
      (indexedTransitionRawBool_eq_true_iff_transition
        tromino periodicStrip periodPositive _ _).mp (step index)
  · rintro ⟨periodPred, states, step⟩
    refine ⟨periodPred,
      fun index =>
        ⟨(indexOfWindow (states index)).val,
          (indexOfWindow (states index)).isLt.trans_le canonicalFits⟩,
      ?_⟩
    intro index
    apply
      (indexedTransitionRawBool_eq_true_iff_transition
        tromino periodicStrip periodPositive _ _).mpr
    simpa using step index

theorem windowState_card_le_indexCount
    (periodicStrip : PeriodicStrip) :
    Fintype.card (WindowState periodicStrip) ≤
      indexCount periodicStrip := by
  rw [indexCount_eq, WindowState.windowState_card]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right
  · omega
  exact Nat.mul_le_mul_left 5
    periodicStrip.motif.toFinset_card_le

/-- A primitive-recursion-friendly sufficient Savitch depth, linear in the
actual binary input encoding length. -/
def stripSearchDepth (periodicStrip : PeriodicStrip) : Nat :=
  21 * ((Complexity.primcodableFinEncoding PeriodicStrip).encode
    periodicStrip).length + 1

/-- A power-of-two ambient state bound.  Padded indices decode to redundant
representatives of semantic frontier states. -/
def stripStateBound (periodicStrip : PeriodicStrip) : Nat :=
  2 ^ stripSearchDepth periodicStrip

theorem indexCount_le_pow_stripSearchDepth
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤ 2 ^ stripSearchDepth periodicStrip := by
  let inputLength :=
    ((Complexity.primcodableFinEncoding PeriodicStrip).encode
      periodicStrip).length
  rw [indexCount_eq]
  calc
    periodicStrip.period *
          9 ^ (5 * periodicStrip.motif.length) ≤
        2 ^ Nat.clog 2 periodicStrip.period *
          (2 ^ 4) ^ (5 * periodicStrip.motif.length) :=
      Nat.mul_le_mul
        (Nat.le_pow_clog Nat.one_lt_two periodicStrip.period)
        (Nat.pow_le_pow_left (by omega) _)
    _ = 2 ^ (Nat.clog 2 periodicStrip.period +
        20 * periodicStrip.motif.length) := by
      rw [← pow_mul, ← pow_add]
      congr 2
      omega
    _ ≤ 2 ^ (21 * inputLength + 1) := by
      apply Nat.pow_le_pow_right (by omega)
      have periodBound :=
        PeriodicStrip.clog_period_le_encoding_length periodicStrip
      have motifBound :=
        PeriodicStrip.motif_length_le_encoding_length periodicStrip
      dsimp only [inputLength] at periodBound motifBound ⊢
      omega
    _ = 2 ^ stripSearchDepth periodicStrip := by
      simp [stripSearchDepth, inputLength]

theorem indexCount_le_stripStateBound
    (periodicStrip : PeriodicStrip) :
    indexCount periodicStrip ≤ stripStateBound periodicStrip := by
  exact indexCount_le_pow_stripSearchDepth periodicStrip

/-- Enumeration-free sparse-frontier decision procedure. -/
def periodicStripTrominoTilingIndexBool
    (tromino : Tromino) (periodicStrip : PeriodicStrip) : Bool :=
  if wellFormed : periodicStrip.IsWellFormed then
    FiniteState.cycleSearchIndexDFSBoolAtDepth
      (stripStateBound periodicStrip)
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
      FiniteState.cycleSearchIndexDFSBoolAtDepth_eq,
      FiniteState.cycleSearchIndexBoolAtDepth_eq_true_iff
        (stripStateBound periodicStrip)
        (stripSearchDepth periodicStrip)
        (indexedTransitionBool tromino periodicStrip wellFormed.2.1)
        (by simp [stripStateBound]),
      paddedIndexed_hasCycle_iff_hasCycle tromino periodicStrip
        wellFormed.2.1 (stripStateBound periodicStrip)
        (indexCount_le_stripStateBound periodicStrip),
      ← WindowState.tileable_iff_hasCycle tromino wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]
  · rw [periodicStripTrominoTilingIndexBool, dif_neg wellFormed]
    simp [PeriodicStripTrominoTiling, wellFormed]

end RawWindowState
end PeriodicStrip
end LeanTrominoes
