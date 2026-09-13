/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryFieldSquareProjectionCompiler
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Two-list Cartesian products of unary columns -/

namespace LeanTrominoes.UnaryFieldCartesian
open UnaryFieldSquareProjection (Side choose)
open UnaryFieldPairPresence (fieldBits)
open UnaryFieldBooleanFilter (selectedValues)

def tags (a b : List Nat) : List Nat := a.map (fun _ => 1) ++ b.map (fun _ => 0)
def controls (a b : List Nat) : List Bool :=
  List.zipWith (· && ·) (fieldBits .first (tags a b)) ((fieldBits .second (tags a b)).map (!·))
def values (side : Side) (a b : List Nat) : List Nat :=
  selectedValues (controls a b) (UnaryFieldSquareProjection.values side (a++b))

theorem selected_map {I : Type} (rows : List I) (p : I → Bool) (f : I → Nat) :
    selectedValues (rows.map p) (rows.map f) = (rows.filter p).map f := by
  rw [UnaryFieldBooleanFilter.selectedValues_eq]
  induction rows with
  | nil => rfl
  | cons row rows ih => cases h : p row <;> simp [DelimitedBinaryWordBooleanFilter.selected,h,ih]

def square {I : Type} (rows : List I) : List (I×I) := rows.flatMap fun a => rows.map fun b => (a,b)

theorem square_map {I J : Type} (rows : List I) (f : I → J) :
    square (rows.map f) = (square rows).map (fun p => (f p.1,f p.2)) := by
  simp [square,List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]

theorem presence_square (side : Side) (rows : List Nat) :
    fieldBits side rows = (square rows).map (fun p => decide (choose side p.1 p.2 ≠ 0)) := by
  cases side <;> simp [fieldBits,UnaryFieldPairPresence.bits,UnaryFieldPairPresence.present,
    DelimitedBinaryWordPairProductMachine.pairs,UnaryFieldBinaryWords.words,UnaryFieldBinaryWords.word,
    square,choose,List.map_const',List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def]
  all_goals exact List.flatMap_congr (fun _ _ => List.map_const'.symm)

theorem projection_square (side : Side) (rows : List Nat) :
    UnaryFieldSquareProjection.values side rows = (square rows).map (fun p => choose side p.1 p.2) := by
  simp [UnaryFieldSquareProjection.values,square,List.map_flatMap,List.map_map,Function.comp_def]

def marked (a b : List Nat) : List (Bool×Nat) := a.map (true,·) ++ b.map (false,·)

theorem tags_marked (a b : List Nat) : tags a b = (marked a b).map (fun p => p.1.toNat) := by
  simp [tags,marked,List.map_map,Function.comp_def]

theorem values_marked (a b : List Nat) : a++b = (marked a b).map Prod.snd := by
  simp [marked,List.map_map]

theorem controls_marked (a b : List Nat) :
    controls a b = (square (marked a b)).map (fun p => p.1.1 && !p.2.1) := by
  have one (side : Side) : fieldBits side (tags a b) =
      (square (marked a b)).map (fun p => choose side p.1.1 p.2.1) := by
    rw [tags_marked,presence_square,square_map,List.map_map]
    apply List.map_congr_left
    rintro ⟨⟨x,u⟩,⟨y,v⟩⟩ _
    cases side <;> cases x <;> cases y <;> rfl
  rw [controls,one,one,List.map_map,List.zipWith_map,List.zipWith_self]
  rfl

theorem filtered_marked (a b : List Nat) :
    ((square (marked a b)).filter (fun p => p.1.1 && !p.2.1)) =
      a.flatMap fun x => b.map fun y => ((true,x),(false,y)) := by
  simp [square,marked,List.flatMap_append,List.flatMap_map,List.map_append,
    List.filter_flatMap,List.filter_append,List.filter_map,Function.comp_def]

/-- Both columns preserve the ordinary row-major Cartesian-product order. -/
theorem values_eq (side : Side) (a b : List Nat) :
    values side a b = a.flatMap fun x => b.map fun y => choose side x y := by
  rw [values,controls_marked,projection_square,values_marked,square_map,List.map_map]
  rw [selected_map,filtered_marked]
  simp [List.map_flatMap,List.map_map,Function.comp_def]

end LeanTrominoes.UnaryFieldCartesian
