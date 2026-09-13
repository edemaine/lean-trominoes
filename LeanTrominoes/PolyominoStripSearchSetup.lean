/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCycleSearch
import LeanTrominoes.Theorem55StripRawDecider

/-! # Compute the graph size and initialize strip cycle search -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def bitsExpr : Expr := (2*var 1+1)*(16*(var 0+2*var 1+1))
def bitsCoefficient : Nat := bitsExpr.weight*(bitsExpr.radius+1)
def countCode : Code := Code.powerTwoCode.comp bitsExpr.code

def searchInputCode : Code := Code.prepend countCode (Code.prepend bitsExpr.code Code.id)
def searchInputCoefficient : Nat := 4*(arithmeticScale+bitsCoefficient+4*(bitsCoefficient+10+1)+1)

def searchCode : Code := cycleCode.comp searchInputCode

def searchBudget (height bound space : Nat) : Nat :=
  cycleBudget (stateBits Bool height bound) space+
    searchInputCoefficient*(space+stateBits Bool height bound+2)

theorem bits_eval (cells : Bool → List Cell) (height bound : Nat) :
    bitsExpr.eval (suffix cells height bound) = stateBits Bool height bound := by
  change (2*bound+1)*(16*(height+2*bound+1)) = _
  simp [stateBits]

theorem bits_noPower : bitsExpr.noPower = true := by simp [bitsExpr,Expr.noPower]

theorem powerTwo_scalar_fits (value : Nat) :
    EvaluatorCodeFits Code.powerTwoCode [value] [2^value] (arithmeticScale*(value+2)) := by
  have input := FiniteState.encodeNat_length_le_of_lt_pow value (value+1)
    (value.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
  have output := FiniteState.encodeNat_length_le_of_lt_pow (2^value) (value+1)
    (Nat.pow_lt_pow_right (by omega) (by omega))
  exact powerTwo_fits value (value+1) input output

theorem count_eval (cells : Bool → List Cell) (height bound : Nat) :
    countCode.eval (suffix cells height bound) = pure [2^stateBits Bool height bound] := by
  simp [countCode,Expr.code_eval,bits_eval,Part.bind_eq_bind]

theorem searchInput_eval (cells : Bool → List Cell) (height bound : Nat) :
    searchInputCode.eval (suffix cells height bound) =
      pure (cycleValues (stateBits Bool height bound) (suffix cells height bound)) := by
  simp [searchInputCode,count_eval,Expr.code_eval,bits_eval,cycleValues]

theorem search_eval (cells : Bool → List Cell) (height bound : Nat) (bounded : Bounded (Raw.tiles cells) bound) :
    searchCode.eval (suffix cells height bound) = pure [(Raw.tilingCheck cells height bound).toNat] := by
  have run := cycle_eval cells height bound (stateBits Bool height bound) bounded
  simpa [searchCode,searchInput_eval,Part.bind_eq_bind,Raw.tilingCheck] using run

theorem searchInput_fits (cells : Bool → List Cell) (height bound : Nat) :
    EvaluatorCodeFits searchInputCode (suffix cells height bound)
      (cycleValues (stateBits Bool height bound) (suffix cells height bound))
      (searchInputCoefficient*(encodedListSpace (suffix cells height bound)+stateBits Bool height bound+2)) := by
  let values := suffix cells height bound
  let bits := stateBits Bool height bound
  let unit := encodedListSpace values+bits+2
  have hu : encodedListSpace values+1 ≤ unit := by omega
  have bitFit := bitsExpr.code_fits_automatic values bits_noPower
  rw [bits_eval] at bitFit
  have bitFit' : EvaluatorCodeFits bitsExpr.code values [bits] (bitsCoefficient*unit) :=
    bitFit.mono (Nat.mul_le_mul_left bitsCoefficient hu)
  have pow := (powerTwo_scalar_fits bits).mono (Nat.mul_le_mul_left arithmeticScale (show bits+2 ≤ unit by omega))
  have count := comp pow bitFit'
  have count' : EvaluatorCodeFits countCode values [2^bits] ((arithmeticScale+bitsCoefficient)*unit) := by
    have eq := Nat.add_mul arithmeticScale bitsCoefficient unit
    rw [← eq] at count
    exact count
  have identity := (EvaluatorCodeFits.id values).mono ((idCost_bound values).trans (Nat.mul_le_mul_left 10 hu))
  have result := prepend_unit hu count' (prepend_unit hu bitFit' identity)
  exact result

theorem search_fits (cells : Bool → List Cell) (height bound : Nat) (bounded : Bounded (Raw.tiles cells) bound) :
    EvaluatorCodeFits searchCode (suffix cells height bound) [(Raw.tilingCheck cells height bound).toNat]
      (searchBudget height bound (encodedListSpace (suffix cells height bound))) := by
  exact comp (cycle_fits cells height bound (stateBits Bool height bound) bounded) (searchInput_fits cells height bound)

end LeanTrominoes.PolyominoStripWindow.Savitch
