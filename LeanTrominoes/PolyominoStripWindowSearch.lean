/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripWindowCorrectness
import LeanTrominoes.FiniteStateCycleSearch

/-! # A finite strip decider and the exact number of window bits -/

namespace LeanTrominoes.PolyominoStripWindow

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (tiles : ι → Polyomino) {height bound : Nat} :
    DecidableRel (LocalWindow.Transition (ValidWindow (height := height) (bound := bound) tiles)) := by
  intro first second
  unfold LocalWindow.Transition
  infer_instance

/-- Executable cycle search; the later machine certificate must enumerate states without storing the graph. -/
def tilingCheck {ι : Type*} [Fintype ι] [DecidableEq ι] (tiles : ι → Polyomino) (height bound : Nat) : Bool :=
  FiniteState.cycleSearchBool (LocalWindow.Transition (ValidWindow (height := height) (bound := bound) tiles))

theorem tilingCheck_correct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tiles : ι → Polyomino} {height bound : Nat} (bounded : Bounded tiles bound) :
    tilingCheck tiles height bound = true ↔ Tileable tiles (horizontalStrip height) := by
  rw [tilingCheck,FiniteState.cycleSearchBool_eq_true_iff]
  exact (tileable_iff_cycle bounded).symm

/-- One bit for each possible placement in each window column. -/
def stateBits (ι : Type*) [Fintype ι] (height bound : Nat) : Nat :=
  (2*bound+1) * (Fintype.card ι * 8 * (height+2*bound+1))

theorem card_slot (ι : Type*) [Fintype ι] (height bound : Nat) :
    Fintype.card (Slot ι height bound) = Fintype.card ι * 8 * (height+2*bound+1) := by
  simp [Slot,show Fintype.card SquareSymmetry = 8 from by decide,Nat.mul_assoc]

theorem card_window (ι : Type*) [Fintype ι] [DecidableEq ι] (height bound : Nat) :
    Fintype.card (Window ι height bound) = 2 ^ stateBits ι height bound := by
  simp only [Window,LocalWindow.Window,Column,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    card_slot, ← pow_mul,stateBits]
  rw [Nat.mul_comm]

theorem savitchDepth_window (ι : Type*) [Fintype ι] [DecidableEq ι] (height bound : Nat) :
    FiniteState.savitchDepth (Window ι height bound) = stateBits ι height bound + 1 := by
  rw [FiniteState.savitchDepth,card_window,Nat.log_pow Nat.one_lt_two]

end LeanTrominoes.PolyominoStripWindow
