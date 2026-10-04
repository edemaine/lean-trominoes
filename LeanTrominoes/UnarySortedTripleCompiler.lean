/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.EncodedUnaryColumnSerialization
import LeanTrominoes.NativeNatBinaryWords
import Mathlib.Data.Finset.Sort

/-! # A verified three-comparison sorting network for footprint codes -/
namespace LeanTrominoes.UnarySortedTriple

def low (a b c : Nat) := min (min a b) (min (max a b) c)
def middle (a b c : Nat) := max (min a b) (min (max a b) c)
def high (a b c : Nat) := max (max a b) c
def sorted (a b c : Nat) := [low a b c,middle a b c,high a b c]

private theorem orderedPair (a b : Nat) : List.Perm [min a b,max a b] [a,b] := by
  rcases le_total a b with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simpa [min_eq_right h,max_eq_left h] using List.Perm.swap a b []

theorem sorted_perm (a b c : Nat) : List.Perm (sorted a b c) [a,b,c] := by
  exact ((orderedPair (min a b) (min (max a b) c)).append_right [max (max a b) c]).trans
    (((orderedPair (max a b) c).cons (min a b)).trans
      ((orderedPair a b).append_right [c]))

theorem sorted_pairwise (a b c : Nat) : (sorted a b c).Pairwise (·≤·) := by
  simp [sorted,List.pairwise_cons]
  dsimp [low,middle,high]
  constructor
  · constructor <;> omega
  · omega

theorem sorted_eq_finset_sort (a b c : Nat) (distinct : [a,b,c].Nodup) :
    sorted a b c = ([a,b,c].toFinset).sort (·≤·) := by
  rw [← List.toFinset_eq_of_perm _ _ (sorted_perm a b c)]
  exact ((List.toFinset_sort (·≤·) ((sorted_perm a b c).nodup_iff.mpr distinct)).mpr
    (sorted_pairwise a b c)).symm

end LeanTrominoes.UnarySortedTriple

noncomputable section
namespace LeanTrominoes.EncodedUnaryColumn
open _root_.Computability Turing
variable {Input Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {encodeInput : Input → List Symbol} {rows : Input → List Index}
  {f g h : Input → Index → Nat}

def minimum (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s i => min (f s i) (g s i)) :=
  (sub a (sub a b)).of_eq (fun s => List.map_congr_left (fun i _ => by dsimp; omega))

def maximum (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g) :
    Compiler encodeInput rows (fun s i => max (f s i) (g s i)) :=
  (add a (sub b a)).of_eq (fun s => List.map_congr_left (fun i _ => by dsimp; omega))

def sortedLow (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g)
    (c : Compiler encodeInput rows h) :
    Compiler encodeInput rows (fun s i => UnarySortedTriple.low (f s i) (g s i) (h s i)) :=
  minimum (minimum a b) (minimum (maximum a b) c)

def sortedMiddle (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g)
    (c : Compiler encodeInput rows h) :
    Compiler encodeInput rows (fun s i => UnarySortedTriple.middle (f s i) (g s i) (h s i)) :=
  maximum (minimum a b) (minimum (maximum a b) c)

def sortedHigh (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g)
    (c : Compiler encodeInput rows h) :
    Compiler encodeInput rows (fun s i => UnarySortedTriple.high (f s i) (g s i) (h s i)) :=
  maximum (maximum a b) c

def sortedTriples (a : Compiler encodeInput rows f) (b : Compiler encodeInput rows g)
    (c : Compiler encodeInput rows h) :
    TM2ComputableInPolyTime encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun s => (rows s).flatMap fun i => UnarySortedTriple.sorted (f s i) (g s i) (h s i)) :=
  triple (sortedLow a b c) (sortedMiddle a b c) (sortedHigh a b c)

end LeanTrominoes.EncodedUnaryColumn
