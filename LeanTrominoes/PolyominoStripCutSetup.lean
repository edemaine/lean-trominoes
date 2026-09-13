/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripSearchSetup
import LeanTrominoes.PolyominoConnectivityExprSpace

/-! # Construct the mask bound and run the disconnectedness checker -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open BoundedArithmetic

abbrev CutFormula := PolyominoConnectivitySearch.Formula.disconnectedDecision

def maskCode : Code := Code.powerTwoCode.comp (Code.get 5)
def cutInputCode : Code := Code.prepend (Code.get 0) (Code.prepend (Code.get 1)
  (Code.prepend maskCode (Code.prepend Code.zero (Code.drop 4))))
def cutCode : Code := CutFormula.code.comp cutInputCode

def cutInputCoefficient : Nat := 4*(10000+4*(20000+4*(arithmeticScale+60000+4*(10000+50000+1)+1)+1)+1)
def cutCoefficient : Nat := PolyominoConnectivitySearch.Formula.disconnectedSpaceConstant*(cutInputCoefficient+1)+cutInputCoefficient

theorem mask_eval (cells : Bool → List Cell) (height bound : Nat) :
    maskCode.eval (suffix cells height bound) = pure [2^(cells true).length] := by
  simp [maskCode,suffix,Arithmetic.input,Part.bind_eq_bind]

theorem cutInput_eval (cells : Bool → List Cell) (height bound : Nat) :
    cutInputCode.eval (suffix cells height bound) =
      pure (Arithmetic.input cells height bound (2^(cells true).length) 0) := by
  have mask := mask_eval cells height bound
  simp only [cutInputCode,Code.prepend_eval_eq,mask]
  simp [suffix,Arithmetic.input]

theorem cut_eval (cells : Bool → List Cell) (height bound : Nat) (nonempty : cells true ≠ []) :
    cutCode.eval (suffix cells height bound) = pure [(PolyominoConnectivitySearch.disconnectedPacked (cells true)).toNat] := by
  simp [cutCode,cutInput_eval,Part.bind_eq_bind,
    PolyominoConnectivitySearch.Formula.disconnected_code_eval cells height bound 0 nonempty]

theorem cutInput_fits (cells : Bool → List Cell) (height bound : Nat) :
    EvaluatorCodeFits cutInputCode (suffix cells height bound)
      (Arithmetic.input cells height bound (2^(cells true).length) 0)
      (cutInputCoefficient*(encodedListSpace (suffix cells height bound)+(cells true).length+2)) := by
  let values := suffix cells height bound
  let count := (cells true).length
  let unit := encodedListSpace values+count+2
  have hu : encodedListSpace values+1 ≤ unit := by omega
  have countFit := get_unit 5 values unit hu
  change EvaluatorCodeFits (Code.get 5) values [count] (60000*unit) at countFit
  have pow := (powerTwo_scalar_fits count).mono (Nat.mul_le_mul_left arithmeticScale (show count+2 ≤ unit by omega))
  have mask := comp pow countFit
  have eq := Nat.add_mul arithmeticScale 60000 unit
  rw [← eq] at mask
  have result := prepend_unit hu (get_unit 0 values unit hu) (prepend_unit hu (get_unit 1 values unit hu)
    (prepend_unit hu mask (prepend_unit hu (zero_unit values unit hu) (drop_unit 4 values unit hu))))
  change EvaluatorCodeFits cutInputCode values (Arithmetic.input cells height bound (2^count) 0)
    (cutInputCoefficient*unit) at result
  exact result

theorem cut_fits (cells : Bool → List Cell) (height bound : Nat) (nonempty : cells true ≠ []) :
    EvaluatorCodeFits cutCode (suffix cells height bound) [(PolyominoConnectivitySearch.disconnectedPacked (cells true)).toNat]
      (cutCoefficient*(encodedListSpace (suffix cells height bound)+(cells true).length+2)) := by
  let unit := encodedListSpace (suffix cells height bound)+(cells true).length+2
  have initial := cutInput_fits cells height bound
  have leaf := PolyominoConnectivitySearch.Formula.disconnected_code_fits cells height bound 0 nonempty
  have result := comp leaf initial
  apply result.mono
  have out := initial.output_space
  change encodedListSpace (Arithmetic.input cells height bound (2^(cells true).length) 0) ≤ cutInputCoefficient*unit at out
  change PolyominoConnectivitySearch.Formula.disconnectedSpaceConstant*
    (encodedListSpace (Arithmetic.input cells height bound (2^(cells true).length) 0)+1)+cutInputCoefficient*unit ≤ cutCoefficient*unit
  have hu : 1 ≤ unit := by omega
  unfold cutCoefficient
  nlinarith [Nat.mul_le_mul_left PolyominoConnectivitySearch.Formula.disconnectedSpaceConstant out]

end LeanTrominoes.PolyominoStripWindow.Savitch
