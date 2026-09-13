/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.RestrictedStripWindow
import LeanTrominoes.Theorem55StripRawDecider
import LeanTrominoes.ThreeTranslationPolyominoes

/-! # Strip transitions which reject rotated background tiles -/

namespace LeanTrominoes.TranslationStrip
open PolyominoStripWindow

def Allowed (kind : Bool) (symmetry : SquareSymmetry) : Prop :=
  kind = true → symmetry = .identity

def Legal (height bound word : Nat) : Prop :=
  ∀ slot ∈ Raw.slots height bound, Raw.selected height bound word (0,slot) = true → Allowed slot.1 slot.2.1

instance (height bound word : Nat) : Decidable (Legal height bound word) := by
  unfold Legal Allowed
  infer_instance

def check (cells : Bool → List Cell) (height bound first second : Nat) : Bool :=
  Raw.check cells height bound first second && decide (Legal height bound first)

theorem legal_iff (height bound word : Nat) :
    Legal height bound word ↔ ∀ slot : Slot Bool height bound,
      decodeWord height bound word 0 slot = true → Allowed slot.1 slot.2.1 := by
  constructor
  · intro h slot selected
    apply h (Raw.eraseSlot slot) ((Raw.mem_slots _).mpr slot.2.2.isLt)
    have eq := Raw.selected_erase word (0,slot)
    simpa only [Raw.erase,Fin.val_zero] using eq.trans selected
  · intro h slot member selected
    let typed : Slot Bool height bound := (slot.1,slot.2.1,⟨slot.2.2,(Raw.mem_slots _).mp member⟩)
    apply h typed
    have eq := Raw.selected_erase word (0,typed)
    exact eq.symm.trans selected

def packedTransition (cells : Bool → List Cell) (height bound first second : Nat) : Prop :=
  LocalWindow.Transition (RestrictedStripWindow.ValidWith (Raw.tiles cells) Allowed)
    (decodeWord height bound first) (decodeWord height bound second)

theorem check_correct (cells : Bool → List Cell) (height bound first second : Nat) :
    check cells height bound first second = true ↔ packedTransition cells height bound first second := by
  rw [check,Bool.and_eq_true,Raw.check_correct,decide_eq_true_eq,legal_iff]
  simp only [packedTransition,PolyominoStripWindow.packedTransition,LocalWindow.Transition,
    RestrictedStripWindow.ValidWith]
  tauto

theorem packed_cycle_iff (cells : Bool → List Cell) (height bound : Nat) :
    FiniteState.HasCycle (fun a b : IndexedState height bound => packedTransition cells height bound a.val b.val) ↔
      FiniteState.HasCycle (LocalWindow.Transition
        (RestrictedStripWindow.ValidWith (height := height) (bound := bound) (Raw.tiles cells) Allowed)) := by
  constructor
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord height bound (states i).val,step⟩
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow (states i),encodeWindow_lt (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i

def tilingCheck (cells : Bool → List Cell) (height bound : Nat) : Bool :=
  FiniteState.cycleSearchIndexDFSBoolAtDepth (2 ^ stateBits Bool height bound)
    (stateBits Bool height bound) (check cells height bound)

theorem tilingCheck_correct (cells : Bool → List Cell) (height bound : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    tilingCheck cells height bound = true ↔
      TileableWith (Raw.tiles cells) (horizontalStrip height) (fun p => Allowed p.kind p.symmetry) := by
  rw [tilingCheck,FiniteState.cycleSearchIndexDFSBoolAtDepth_eq]
  have search := FiniteState.cycleSearchIndexBoolAtDepth_eq_true_iff
    (2 ^ stateBits Bool height bound) (stateBits Bool height bound) (check cells height bound) (by rfl)
  have relation_eq : FiniteState.IndexedRelation (2 ^ stateBits Bool height bound) (check cells height bound) =
      (fun a b : IndexedState height bound => packedTransition cells height bound a.val b.val) := by
    funext a b
    exact propext (check_correct cells height bound a.val b.val)
  rw [relation_eq] at search
  exact search.trans ((packed_cycle_iff cells height bound).trans
    (RestrictedStripWindow.tileable_iff_cycle Allowed bounded).symm)

end LeanTrominoes.TranslationStrip
