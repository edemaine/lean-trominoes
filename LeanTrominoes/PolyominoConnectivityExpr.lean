/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivityCoordinateExpr
import LeanTrominoes.PolyominoConnectivityIndexedCut
import LeanTrominoes.PolyominoStripArithmeticInput

/-! # Bounded arithmetic formulas for disconnectedness of the input tile -/

namespace LeanTrominoes.PolyominoConnectivitySearch.Formula
open BoundedArithmetic BoundedArithmetic.Expr
open PolyominoStripWindow

def qCode (depth indexField axis : Nat) : Expr :=
  .load (.literal (depth+6)+2*var (depth+4)+2*var indexField+.literal axis)

theorem qCode_eval (cells : Bool → List Cell) (height bound first second : Nat)
    (front : List Nat) (indexField index : Nat) (axis : Fin 2)
    (hj : (front ++ Arithmetic.input cells height bound first second)[indexField]?.getD 0 = index)
    (hi : index < (cells true).length) :
    (qCode front.length indexField axis.val).eval (front ++ Arithmetic.input cells height bound first second) =
      (PeriodicStripFlatEncoding.cellFields (cells true)[index])[axis.val]?.getD 0 := by
  have hp := Arithmetic.header_get cells height bound first second front 4 (by decide)
  change ((front ++ Arithmetic.input cells height bound first second)[front.length+6+
    2*((front ++ Arithmetic.input cells height bound first second)[front.length+4]?.getD 0)+
    2*((front ++ Arithmetic.input cells height bound first second)[indexField]?.getD 0)+axis.val]?.getD 0) = _
  rw [hj,hp]
  have field := Arithmetic.cell_field cells height bound first second front true index axis hi
  simpa [Arithmetic.cellBase,Nat.add_assoc] using field

def pairNeighbours : Expr := neighbours (qCode 3 1 0) (qCode 3 1 1) (qCode 3 0 0) (qCode 3 0 1)

theorem pairNeighbours_truth (cells : Bool → List Cell) (height bound first second word i j : Nat)
    (hi : i < (cells true).length) (hj : j < (cells true).length) :
    pairNeighbours.Truth (j :: i :: word :: Arithmetic.input cells height bound first second) ↔
      (cells true)[i] = (cells true)[j] ∨ Cell.SideAdjacent (cells true)[i] (cells true)[j] := by
  have hx := qCode_eval cells height bound first second [j,i,word] 1 i (0 : Fin 2) rfl hi
  have hy := qCode_eval cells height bound first second [j,i,word] 1 i (1 : Fin 2) rfl hi
  have hu := qCode_eval cells height bound first second [j,i,word] 0 j (0 : Fin 2) rfl hj
  have hv := qCode_eval cells height bound first second [j,i,word] 0 j (1 : Fin 2) rfl hj
  exact neighbours_truth _ _ _ _ _ _ _ hx hy hu hv

/-- Environment: cut word followed by the complete strip input. -/
def cut : Expr :=
  andE (existsE (var 6) (.testBit (var 1) (var 0)))
    (andE (existsE (var 6) (notE (.testBit (var 1) (var 0))))
      (.all (var 6) (.all (var 7)
        (impE (.testBit (var 2) (var 1)) (impE pairNeighbours (.testBit (var 2) (var 0)))))))

theorem cut_truth (cells : Bool → List Cell) (height bound first second word : Nat) :
    cut.Truth (word :: Arithmetic.input cells height bound first second) ↔ IndexedCut (cells true) word := by
  have count : (var 6).eval (word :: Arithmetic.input cells height bound first second) = (cells true).length := rfl
  have count' (i : Nat) : (var 7).eval (i :: word :: Arithmetic.input cells height bound first second) = (cells true).length := rfl
  simp only [cut,truth_and,truth_exists,truth_not,truth_bit,truth_all,truth_imp,count,count']
  change ((∃ i < (cells true).length, word.testBit i = true) ∧
    (∃ i < (cells true).length, ¬ word.testBit i = true) ∧
    ∀ i < (cells true).length, ∀ j < (cells true).length, word.testBit i = true →
      pairNeighbours.Truth (j :: i :: word :: Arithmetic.input cells height bound first second) → word.testBit j = true) ↔ _
  unfold IndexedCut
  apply and_congr Iff.rfl
  apply and_congr
  · simp only [Bool.not_eq_true]
  · apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [pairNeighbours_truth cells height bound first second word i j hi hj]

/-- Field 2 supplies the mask bound; its binary size is linear in the number of cells. -/
def disconnected : Expr := existsE (var 2) cut

theorem disconnected_truth (cells : Bool → List Cell) (height bound second : Nat)
    (nonempty : cells true ≠ []) :
    disconnected.Truth (Arithmetic.input cells height bound (2^(cells true).length) second) ↔
      ¬ Polyomino.IsConnected (cells true).toFinset := by
  rw [disconnected,truth_exists]
  have limit : (var 2).eval (Arithmetic.input cells height bound (2^(cells true).length) second) = 2^(cells true).length := rfl
  rw [limit]
  simp only [cut_truth]
  exact exists_indexedCut_iff (cells true) nonempty

theorem qCode_noPower (depth indexField axis : Nat) : (qCode depth indexField axis).noPower = true := by
  simp [qCode,Expr.noPower]

theorem cut_noPower : cut.noPower = true := by
  have pair : pairNeighbours.noPower = true := neighbours_noPower _ _ _ _
    (qCode_noPower _ _ _) (qCode_noPower _ _ _) (qCode_noPower _ _ _) (qCode_noPower _ _ _)
  simp [cut,andE,existsE,notE,eqE,impE,Expr.noPower,pair]

theorem disconnected_noPower : disconnected.noPower = true := by
  simp [disconnected,existsE,notE,eqE,Expr.noPower,cut_noPower]

end LeanTrominoes.PolyominoConnectivitySearch.Formula
