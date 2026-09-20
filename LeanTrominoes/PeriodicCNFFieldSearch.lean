/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldCycleSearch
import LeanTrominoes.PolyominoStripSearchSetup

/-! # Compute the graph size and initialize CNF cycle search -/

namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open PeriodicCNFFlatEncoding
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic BoundedArithmetic.Expr

def bits (f : PeriodicCNF Nat) : Nat := 3*(formulaFields f).length

def result (f : PeriodicCNF Nat) : Bool :=
  cycleSearchIndexDFSBoolAtDepth (2^bits f) (bits f) (FieldPredicate.check f)

theorem result_correct (f : PeriodicCNF Nat) : result f = true ↔ LocalPeriodicCNF1DSAT f := by
  rw [result,cycleSearchIndexDFSBoolAtDepth_eq]
  exact (cycleSearchIndexBoolAtDepth_eq_true_iff (2^bits f) (bits f) (FieldPredicate.check f) le_rfl).trans
    (FieldPredicate.cycle_iff f)

def bitsExpr : Expr := 3*var 0
def bitsCoefficient : Nat := bitsExpr.weight*(bitsExpr.radius+1)
def countCode : Code := Code.powerTwoCode.comp bitsExpr.code

def searchInputCode : Code := Code.prepend countCode (Code.prepend bitsExpr.code Code.id)
def searchInputCoefficient : Nat := 4*(arithmeticScale+bitsCoefficient+4*(bitsCoefficient+10+1)+1)

def searchCode : Code := cycleCode.comp searchInputCode

def searchBudget (f : PeriodicCNF Nat) (space : Nat) : Nat :=
  cycleBudget (bits f) space+
    searchInputCoefficient*(space+bits f+2)

theorem bits_eval (f : PeriodicCNF Nat) :
    bitsExpr.eval (suffix f) = bits f := by
  rfl

theorem bits_noPower : bitsExpr.noPower = true := by simp [bitsExpr,Expr.noPower]

theorem count_eval (f : PeriodicCNF Nat) :
    countCode.eval (suffix f) = pure [2^bits f] := by
  simp [countCode,Expr.code_eval,bits_eval,Part.bind_eq_bind]

theorem searchInput_eval (f : PeriodicCNF Nat) :
    searchInputCode.eval (suffix f) =
      pure (cycleValues (bits f) (suffix f)) := by
  simp [searchInputCode,count_eval,Expr.code_eval,bits_eval,cycleValues]

theorem search_eval (f : PeriodicCNF Nat)  :
    searchCode.eval (suffix f) = pure [(result f).toNat] := by
  have run := cycle_eval f (bits f)
  simpa [searchCode,searchInput_eval,Part.bind_eq_bind,result] using run

theorem searchInput_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits searchInputCode (suffix f)
      (cycleValues (bits f) (suffix f))
      (searchInputCoefficient*(encodedListSpace (suffix f)+bits f+2)) := by
  let values := suffix f
  let bits := bits f
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

theorem search_fits (f : PeriodicCNF Nat)  :
    EvaluatorCodeFits searchCode (suffix f) [(result f).toNat]
      (searchBudget f (encodedListSpace (suffix f))) := by
  exact comp (cycle_fits f (bits f)) (searchInput_fits f)

end LeanTrominoes.PeriodicCNF.FieldSavitch
