/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldSearch
import LeanTrominoes.PeriodicCNFFieldBudgetPolynomial

/-! # Polynomial evaluator space for the complete local 1D CNF decider -/
namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open PeriodicCNFFlatEncoding FlatScanner
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial BoundedArithmetic

def scannerProject (i : Nat) : Code := (Code.get i).comp scannerCode

def scannerProjectCoefficient (i : Nat) : Nat :=
  (10000*(i+1))*(scannerWeight+1)+scannerWeight

def suffixCode : Code := Code.prepend (scannerProject 0)
  (Code.prepend (scannerProject 3) (Code.prepend (scannerProject 4)
    (Code.prepend Code.zero (Code.prepend Code.zero Code.id))))

def suffixCoefficient : Nat :=
  4*(scannerProjectCoefficient 0+4*(scannerProjectCoefficient 3+
    4*(scannerProjectCoefficient 4+4*(10000+4*(10000+10+1)+1)+1)+1)+1)

theorem fields_space (f : PeriodicCNF Nat) :
    encodedListSpace (formulaFields f) = (finEncoding.encode f).length := by
  rw [finEncoding_encode_length,encodedListSpace_eq_sum]

theorem suffixCode_eval (f : PeriodicCNF Nat) : suffixCode.eval (formulaFields f) = pure (suffix f) := by
  simp [suffixCode,scannerProject,scannerCode_eval,Part.bind_eq_bind,suffix,FieldPredicate.input,FieldPredicate.context]

theorem suffixCode_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits suffixCode (formulaFields f) (suffix f)
      (suffixCoefficient*((finEncoding.encode f).length+1)) := by
  let v := formulaFields f
  have scan := scannerCode_fits f
  rw [← fields_space] at scan
  have proj (i : Nat) := comp_linear
    (get_linear i [(formulaFields f).length,0,0,clauseMarks 1 f.clauses,literalMarks 1 f.clauses]) scan
  have z := zero_unit v (encodedListSpace v+1) le_rfl
  have ident := (EvaluatorCodeFits.id v).mono (idCost_bound v)
  have fit := prepend_linear (proj 0) (prepend_linear (proj 3) (prepend_linear (proj 4)
    (prepend_linear z (prepend_linear z ident))))
  change EvaluatorCodeFits suffixCode v (suffix f) (suffixCoefficient*(encodedListSpace v+1)) at fit
  simpa only [v,fields_space] using fit

theorem suffix_space (f : PeriodicCNF Nat) :
    encodedListSpace (suffix f) ≤ 4*(finEncoding.encode f).length+5 := by
  have masks := masks_bound f (formulaFields f).length
  change _ ∧ (scan f).clauseMask < _ ∧ (scan f).literalMask < _ at masks
  rw [(scan_masks f).1,(scan_masks f).2] at masks
  have cm := encodeNat_length_le_of_lt_pow _ _ masks.2.1
  have lm := encodeNat_length_le_of_lt_pow _ _ masks.2.2
  have n := encodeNat_length_le_self (formulaFields f).length
  have len := list_length_le_encodedListSpace (formulaFields f)
  rw [fields_space] at len
  have hz : (Computability.encodeNat 0).length = 0 := rfl
  simp only [suffix,FieldPredicate.input,FieldPredicate.context,List.cons_append,List.nil_append,
    encodedListSpace_cons,hz,fields_space]
  omega

theorem bits_bound (f : PeriodicCNF Nat) : bits f ≤ 3*(finEncoding.encode f).length := by
  unfold bits
  exact Nat.mul_le_mul_left 3 (by simpa only [fields_space] using list_length_le_encodedListSpace (formulaFields f))

def decideCode : Code := searchCode.comp suffixCode

theorem decide_eval (f : PeriodicCNF Nat) : decideCode.eval (formulaFields f) = pure [(result f).toNat] := by
  simp [decideCode,suffixCode_eval,search_eval,Part.bind_eq_bind]

noncomputable def spacePolynomial : Polynomial Nat :=
  cycleBudgetPolynomial (3*X) (4*X+5)+
    C searchInputCoefficient*((4*X+5)+3*X+2)+C suffixCoefficient*(X+1)

theorem decide_fits (f : PeriodicCNF Nat) :
    EvaluatorCodeFits decideCode (formulaFields f) [(result f).toNat]
      (spacePolynomial.eval (finEncoding.encode f).length) := by
  have fit := EvaluatorCodeFits.comp (search_fits f) (suffixCode_fits f)
  apply fit.mono
  have cycle := cycleBudget_mono (bits_bound f) (suffix_space f)
  have linear := Nat.mul_le_mul_left searchInputCoefficient
    (show encodedListSpace (suffix f)+bits f+2 ≤
      (4*(finEncoding.encode f).length+5)+3*(finEncoding.encode f).length+2 by
        have a := suffix_space f
        have b := bits_bound f
        omega)
  simp only [spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,cycleBudgetPolynomial_eval]
  unfold searchBudget
  omega

end LeanTrominoes.PeriodicCNF.FieldSavitch
