/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripCompilerScanSpace

/-! # Workspace certificate for the uncovered-strip compiler -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
open BoundedArithmetic BoundedArithmetic.Expr
open Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits

def exprCoefficient (e : Expr) : Nat := e.weight*(e.radius+1)
def extractCoefficient : Nat := 4*(20000+4*(10000+exprCoefficient baseExpr+1)+1)
def unpackCoefficient : Nat := 60000+100000*(2*PackedFields.stepCoefficient+2)
def finishUnit (input : PeriodicStripTrominoPrefill) : Nat :=
  (2*(input.period*input.height)+3)*(scanSpace input+base input+input.period*input.height+20)
def finishCoefficient : Nat :=
  4*(50000+4*(60000+4*(exprCoefficient (var 1/2)+unpackCoefficient+extractCoefficient+1)+1)+1)

theorem finishUnit_large (input : PeriodicStripTrominoPrefill) :
    scanSpace input+1 ≤ finishUnit input ∧ 2*(input.period*input.height)+1 ≤ finishUnit input := by
  constructor
  · calc
      scanSpace input+1 ≤ 1*(scanSpace input+base input+input.period*input.height+20) := by omega
      _ ≤ finishUnit input := Nat.mul_le_mul_right _ (by omega)
  · calc
      2*(input.period*input.height)+1 ≤ (2*(input.period*input.height)+3)*1 := by omega
      _ ≤ finishUnit input := Nat.mul_le_mul_left _ (by omega)

theorem finish_fits (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) (n : Nat) (hn : n ≤ input.period*input.height) :
    EvaluatorCodeFits finishCode (payload t input n)
      ([input.height,input.period,(emitted t input n).length]++records t input n)
      (finishCoefficient*finishUnit input) := by
  let values := payload t input n
  let digits := (records t input n).reverse
  let word := PackedFields.pack (base input) digits
  let unit := finishUnit input
  have hu : encodedListSpace values+1 ≤ unit :=
    (Nat.add_le_add_right (payload_space t input hh n hn) 1).trans (finishUnit_large input).1
  have bounded : ∀ a ∈ digits, a < base input := by
    simpa [digits] using records_bounded t input hh n hn
  have count : digits.length ≤ 2*(input.period*input.height) := by
    simpa [digits,records_length] using Nat.mul_le_mul_left 2 ((emitted_length_le t input n).trans hn)
  have bits : (Computability.encodeNat word).length ≤ scanSpace input := by
    have h := payload_space t input hh n hn
    simp only [payload,List.cons_append,List.nil_append,encodedListSpace_cons] at h
    exact le_trans (by dsimp [word,digits]; omega) h
  have orbit : PackedFields.orbitBudget word (base input) digits.length ≤ unit := by
    have hb := nat_bits_le (base input)
    unfold PackedFields.orbitBudget
    exact (Nat.mul_le_mul (by omega) (show
      (Computability.encodeNat word).length+(Computability.encodeNat (base input)).length+1 ≤
      scanSpace input+base input+input.period*input.height+20 by omega))
  have counter : (Computability.encodeNat digits.length).length ≤ unit :=
    (nat_bits_le digits.length).trans ((Nat.add_le_add_right count 1).trans (finishUnit_large input).2)
  have positive : 1 ≤ unit := by have := (finishUnit_large input).1; dsimp [unit]; omega
  have unpack := (PackedFields.unpack_fits (base input) digits bounded).mono
    (show PackedFields.unpackBudget word (base input) digits.length ≤ unpackCoefficient*unit by
      unfold PackedFields.unpackBudget iterationBudget unpackCoefficient
      nlinarith [Nat.mul_le_mul_left PackedFields.stepCoefficient (show
        PackedFields.orbitBudget word (base input) digits.length+1 ≤ 2*unit by omega)])
  have extract := prepend_linear (get_linear 1 values)
    (prepend_linear (get_linear 0 values) (baseExpr.code_fits_automatic values (by simp [baseExpr,Expr.noPower])))
  have extractEq : [values[1]?.getD 0,values[0]?.getD 0,baseExpr.eval values] =
      [digits.length,word,base input] := by
    simp [values,payload,digits,word,fields,CompletionStripEncoding.fields,baseExpr,base,Expr.eval,Op.eval]
  change EvaluatorCodeFits _ values [values[1]?.getD 0,values[0]?.getD 0,baseExpr.eval values]
    (extractCoefficient*(encodedListSpace values+1)) at extract
  rw [extractEq] at extract
  have extractBound := extract.mono (Nat.mul_le_mul_left extractCoefficient hu)
  have core := (comp unpack extractBound).mono (show
    unpackCoefficient*unit+extractCoefficient*unit ≤ (unpackCoefficient+extractCoefficient)*unit by simp [Nat.add_mul])
  have countFit := ((var 1/2).code_fits_automatic values (by simp [Expr.noPower])).mono
    (Nat.mul_le_mul_left (exprCoefficient (var 1/2)) hu)
  have result := prepend_unit hu (get_unit 4 values unit hu)
    (prepend_unit hu (get_unit 5 values unit hu) (prepend_unit hu countFit core))
  change EvaluatorCodeFits finishCode values _ (finishCoefficient*unit) at result
  simpa [values,payload,fields,CompletionStripEncoding.fields,digits,records_length,Expr.eval] using result


def initializeCoefficient : Nat :=
  4*(exprCoefficient (var 1*var 2)+4*(10000+4*(10000+4*(10000+10000+1)+1)+1)+1)

theorem initialize_fits (input : PeriodicStripTrominoPrefill) :
    EvaluatorCodeFits initializeCode (fields input)
      ((input.period*input.height)::([0,0,0]++fields input))
      (initializeCoefficient*(encodedListSpace (fields input)+1)) := by
  let values := fields input
  have ident : EvaluatorCodeFits Code.id values values (10000*(encodedListSpace values+1)) := by
    apply (EvaluatorCodeFits.id values).mono
    have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
    simp [idCost,tailCost,zeroPrimeCost,encodedListSpace_cons,zeroBits]
    omega
  have zero := zero_unit values (encodedListSpace values+1) le_rfl
  have result := prepend_linear ((var 1*var 2).code_fits_automatic values (by simp))
    (prepend_linear zero (prepend_linear zero (prepend_linear zero ident)))
  change EvaluatorCodeFits initializeCode values _
    (initializeCoefficient*(encodedListSpace values+1)) at result
  simpa [values,fields,CompletionStripEncoding.fields,Nat.mul_comm] using result

def compileBudget (t : Tromino) (input : PeriodicStripTrominoPrefill) : Nat :=
  finishCoefficient*finishUnit input +
    (iterationBudget (stepCoefficient t*(scanSpace input+1))
      (Computability.encodeNat (input.period*input.height)).length +
    initializeCoefficient*(encodedListSpace (fields input)+1))

theorem compile_fits (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (hh : 0 < input.height) :
    EvaluatorCodeFits (compileCode t) (fields input)
      (PeriodicStripFlatEncoding.stripFields (compiledStrip t input)) (compileBudget t input) := by
  exact comp (finish_fits t input hh _ le_rfl) (comp (scan_fits t input hh) (initialize_fits input))

theorem finishUnit_polynomial (input : PeriodicStripTrominoPrefill) :
    finishUnit input ≤ 150*((CompletionStripEncoding.finEncoding.encode input).length+1)^5 := by
  let n := (CompletionStripEncoding.finEncoding.encode input).length
  have hh : input.height ≤ n := CompletionStripEncoding.height_le_length input
  have hp : input.period ≤ n := CompletionStripEncoding.period_le_length input
  have area : input.period*input.height ≤ n*n := Nat.mul_le_mul hp hh
  have scan : scanSpace input ≤ 20*(n+1)^3 := scanSpace_polynomial input
  have radix : base input ≤ 4*n+2 := by unfold base; omega
  have first : 2*(input.period*input.height)+3 ≤ 3*(n+1)^2 := by nlinarith
  have second : scanSpace input+base input+input.period*input.height+20 ≤ 50*(n+1)^3 := by nlinarith
  exact (Nat.mul_le_mul first second).trans_eq (by ring)


def compileCoefficient (t : Tromino) : Nat :=
  150*finishCoefficient+100000*(21*stepCoefficient t+3)+6*initializeCoefficient

theorem compileBudget_polynomial (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    compileBudget t input ≤ compileCoefficient t*
      ((CompletionStripEncoding.finEncoding.encode input).length+1)^5 := by
  let n := (CompletionStripEncoding.finEncoding.encode input).length
  have finish : finishUnit input ≤ 150*(n+1)^5 := finishUnit_polynomial input
  have scan : scanSpace input ≤ 20*(n+1)^3 := scanSpace_polynomial input
  have raw : encodedListSpace (fields input) ≤ 3*n+5 := raw_space_le input
  have area : input.period*input.height ≤ n*n :=
    Nat.mul_le_mul (CompletionStripEncoding.period_le_length input) (CompletionStripEncoding.height_le_length input)
  have counter := nat_bits_le (input.period*input.height)
  have cube : (n+1)^3 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have square : n*n+2 ≤ 2*(n+1)^5 := by nlinarith
  have scan' : scanSpace input+1 ≤ 21*(n+1)^5 := by nlinarith
  have raw' : encodedListSpace (fields input)+1 ≤ 6*(n+1)^5 := by nlinarith
  have hfinish := Nat.mul_le_mul_left finishCoefficient finish
  have hscan := Nat.mul_le_mul_left (stepCoefficient t) scan'
  have hraw := Nat.mul_le_mul_left initializeCoefficient raw'
  unfold compileBudget iterationBudget compileCoefficient
  change _ ≤ (150*finishCoefficient+100000*(21*stepCoefficient t+3)+6*initializeCoefficient)*(n+1)^5
  nlinarith

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw.Compiler
