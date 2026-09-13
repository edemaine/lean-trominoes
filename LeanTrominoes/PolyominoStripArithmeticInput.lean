/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripArithmeticGeometry
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # Flat fields for the variable-tile transition formula -/

namespace LeanTrominoes.PolyominoStripWindow.Arithmetic

def coordinates (cells : List Cell) : List Nat := cells.flatMap PeriodicStripFlatEncoding.cellFields

theorem coordinates_length (cells : List Cell) : (coordinates cells).length = 2*cells.length := by
  induction cells with
  | nil => rfl
  | cons c cells ih => simp [coordinates,PeriodicStripFlatEncoding.cellFields] at *; omega

def input (cells : Bool → List Cell) (height bound first second : Nat) : List Nat :=
  [height,bound,first,second,(cells false).length,(cells true).length] ++
    coordinates (cells false) ++ coordinates (cells true)

def cellBase (cells : Bool → List Cell) (kind : Bool) : Nat :=
  if kind then 6+2*(cells false).length else 6

private theorem coordinates_get (cells : List Cell) (suffix : List Nat) (index : Nat) (axis : Fin 2)
    (hi : index < cells.length) :
    ((coordinates cells ++ suffix)[2*index+axis.val]?.getD 0) =
      (PeriodicStripFlatEncoding.cellFields cells[index])[axis.val]?.getD 0 := by
  induction cells generalizing index with
  | nil => simp at hi
  | cons c cells ih =>
    cases index with
    | zero =>
      fin_cases axis <;> simp [coordinates,PeriodicStripFlatEncoding.cellFields]
    | succ index =>
      have h := ih index (by simpa using hi)
      have address : 2*(index+1)+axis.val = (2*index+axis.val)+1+1 := by omega
      simpa [coordinates,PeriodicStripFlatEncoding.cellFields,address] using h

theorem prefix_get (front values : List Nat) (index : Nat) :
    ((front++values)[front.length+index]?.getD 0) = values[index]?.getD 0 := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem header_get (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (field : Nat) (hf : field < 6) :
    ((front ++ input cells height bound first second)[front.length+field]?.getD 0) =
      ([height,bound,first,second,(cells false).length,(cells true).length][field]?.getD 0) := by
  rw [prefix_get]
  simp only [input,List.append_assoc]
  rw [List.getElem?_append_left (by simpa using hf)]

/-- Read an oriented source coordinate without decoding a paired list. -/
theorem cell_field (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (kind : Bool) (index : Nat) (axis : Fin 2) (hi : index < (cells kind).length) :
    ((front ++ input cells height bound first second)[front.length+cellBase cells kind+2*index+axis.val]?.getD 0) =
      (PeriodicStripFlatEncoding.cellFields (cells kind)[index])[axis.val]?.getD 0 := by
  cases kind with
  | false =>
    let header := front ++ [height,bound,first,second,(cells false).length,(cells true).length]
    have indexEq : front.length+cellBase cells false+2*index+axis.val = header.length+(2*index+axis.val) := by
      simp [header,cellBase]
      omega
    rw [indexEq]
    have read := (prefix_get header (coordinates (cells false) ++ coordinates (cells true)) (2*index+axis.val)).trans
      (coordinates_get (cells false) (coordinates (cells true)) index axis hi)
    simpa only [header,input,List.append_assoc] using read
  | true =>
    let header := front ++ [height,bound,first,second,(cells false).length,(cells true).length] ++ coordinates (cells false)
    have indexEq : front.length+cellBase cells true+2*index+axis.val = header.length+(2*index+axis.val) := by
      simp [header,cellBase,coordinates_length]
      omega
    rw [indexEq]
    have read := prefix_get header (coordinates (cells true)) (2*index+axis.val)
    have coord := coordinates_get (cells true) [] index axis hi
    simp only [List.append_nil] at coord
    simpa only [header,input,List.append_assoc] using read.trans coord

end LeanTrominoes.PolyominoStripWindow.Arithmetic
