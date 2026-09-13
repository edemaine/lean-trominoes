/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripWindowSearch
import Mathlib.Data.BitVec

/-! # Packed binary words for two-tile strip frontiers -/

namespace LeanTrominoes.PolyominoStripWindow

def symmetries : List SquareSymmetry :=
  [.identity,.rotate90,.rotate180,.rotate270,.reflectX,.reflectDiagonal,.reflectY,.reflectAntidiagonal]

theorem mem_symmetries (s : SquareSymmetry) : s ∈ symmetries := by cases s <;> simp [symmetries]

/-- Enumerate placement bits, never the exponentially larger list of states. -/
def keys (height bound : Nat) : List (Candidate Bool height bound) :=
  (List.finRange (2*bound+1)).flatMap fun column =>
    [false,true].flatMap fun kind => symmetries.flatMap fun symmetry =>
      (List.finRange (height+2*bound+1)).map fun y => (column,(kind,symmetry,y))

theorem mem_keys {height bound : Nat} (a : Candidate Bool height bound) : a ∈ keys height bound := by
  rcases a with ⟨column,kind,symmetry,y⟩
  simp only [keys,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  refine ⟨column,kind,by cases kind <;> simp,symmetry,mem_symmetries symmetry,y,rfl⟩

theorem keys_length (height bound : Nat) : (keys height bound).length = stateBits Bool height bound := by
  simp [keys,symmetries,List.length_flatMap,List.sum_replicate,stateBits]
  ring

def decodeWord (height bound word : Nat) : Window Bool height bound :=
  fun column slot => word.testBit ((keys height bound).idxOf (column,slot))

def encodeWindow {height bound : Nat} (window : Window Bool height bound) : Nat :=
  (BitVec.ofBoolListLE ((keys height bound).map fun a => window a.1 a.2)).toNat

/-- Encoding and reading a bit reconstructs the exact semantic window. -/
theorem decodeWord_encodeWindow {height bound : Nat} (window : Window Bool height bound) :
    decodeWord height bound (encodeWindow window) = window := by
  funext column slot
  simp only [decodeWord,encodeWindow,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_idxOf (mem_keys (column,slot))]
  rfl

theorem encodeWindow_lt {height bound : Nat} (window : Window Bool height bound) :
    encodeWindow window < 2 ^ stateBits Bool height bound := by
  have h := (BitVec.ofBoolListLE ((keys height bound).map fun a => window a.1 a.2)).isLt
  simpa [encodeWindow,keys_length] using h

/-- The relation only decodes the two current binary words. -/
def packedTransition (tiles : Bool → Polyomino) (height bound first second : Nat) : Prop :=
  LocalWindow.Transition (ValidWindow tiles) (decodeWord height bound first) (decodeWord height bound second)

instance (tiles : Bool → Polyomino) (height bound first second : Nat) :
    Decidable (packedTransition tiles height bound first second) := by
  unfold packedTransition
  infer_instance

def IndexedState (height bound : Nat) := Fin (2 ^ stateBits Bool height bound)

theorem packed_cycle_iff (tiles : Bool → Polyomino) (height bound : Nat) :
    FiniteState.HasCycle (fun a b : IndexedState height bound => packedTransition tiles height bound a.val b.val) ↔
      FiniteState.HasCycle (LocalWindow.Transition (ValidWindow (height := height) (bound := bound) tiles)) := by
  constructor
  · rintro ⟨period,states,step⟩
    exact ⟨period,fun i => decodeWord height bound (states i).val,step⟩
  · rintro ⟨period,states,step⟩
    refine ⟨period,fun i => ⟨encodeWindow (states i),encodeWindow_lt (states i)⟩,?_⟩
    intro i
    simpa only [packedTransition,decodeWord_encodeWindow] using step i

end LeanTrominoes.PolyominoStripWindow
