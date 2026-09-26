/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMFieldSearch
import LeanTrominoes.PeriodicThreeDMFieldBudgetPolynomial

/-! # Native polynomial-space matching search for local horizontal 3DM -/
namespace LeanTrominoes.PeriodicThreeDM.FieldSavitch
open FlatEncoding Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial BoundedArithmetic

def suffixCode : Code := Code.prepend (Code.get 3)
  (Code.prepend Code.zero (Code.prepend Code.zero (Code.prepend Code.zero (Code.prepend Code.zero Code.id))))

def suffixCoefficient : Nat := 4*(40000+4*(10000+4*(10000+4*(10000+4*(10000+10+1)+1)+1)+1)+1)

theorem fields_space (p : PeriodicThreeDM) : encodedListSpace (fields p) = (finEncoding.encode p).length := by
  change encodedListSpace (fields p) = (PeriodicCNFFlatEncoding.encodeNatFields (fields p)).length
  rw [PeriodicCNFFlatEncoding.encodeNatFields_length,encodedListSpace_eq_sum]

theorem suffixCode_eval (p : PeriodicThreeDM) : suffixCode.eval (fields p) = pure (suffix p) := by
  simp [suffixCode,suffix,FieldPredicate.input,FieldPredicate.context,fields]

theorem suffixCode_fits (p : PeriodicThreeDM) :
    EvaluatorCodeFits suffixCode (fields p) (suffix p) (suffixCoefficient*((finEncoding.encode p).length+1)) := by
  let v := fields p
  have z := zero_unit v (encodedListSpace v+1) le_rfl
  have ident := (EvaluatorCodeFits.id v).mono (idCost_bound v)
  have fit := prepend_linear (get_linear 3 v)
    (prepend_linear z (prepend_linear z (prepend_linear z (prepend_linear z ident))))
  change EvaluatorCodeFits suffixCode v (suffix p) (suffixCoefficient*(encodedListSpace v+1)) at fit
  simpa only [v,fields_space] using fit

theorem triples_bound (p : PeriodicThreeDM) : p.triples.length ≤ (finEncoding.encode p).length := by
  have h := list_length_le_encodedListSpace (fields p)
  rw [fields_length,fields_space] at h
  omega

theorem suffix_space (p : PeriodicThreeDM) : encodedListSpace (suffix p) ≤ 2*(finEncoding.encode p).length+5 := by
  have bits := encodeNat_length_le_self p.triples.length
  have bound := triples_bound p
  have hz : (_root_.Computability.encodeNat 0).length = 0 := rfl
  simp only [suffix,FieldPredicate.input,FieldPredicate.context,List.cons_append,List.nil_append,
    encodedListSpace_cons,hz,fields_space]
  omega

theorem bits_bound (p : PeriodicThreeDM) : bits p ≤ 3*(finEncoding.encode p).length :=
  Nat.mul_le_mul_left 3 (triples_bound p)

def decideCode : Code := searchCode.comp suffixCode

theorem decide_eval (p : PeriodicThreeDM) : decideCode.eval (fields p) = pure [(result p).toNat] := by
  simp [decideCode,suffixCode_eval,search_eval,Part.bind_eq_bind]

noncomputable def spacePolynomial : Polynomial Nat :=
  cycleBudgetPolynomial (3*X) (2*X+5)+C searchInputCoefficient*((2*X+5)+3*X+2)+C suffixCoefficient*(X+1)

theorem decide_fits (p : PeriodicThreeDM) :
    EvaluatorCodeFits decideCode (fields p) [(result p).toNat]
      (spacePolynomial.eval (finEncoding.encode p).length) := by
  have fit := EvaluatorCodeFits.comp (search_fits p) (suffixCode_fits p)
  apply fit.mono
  have cycle := cycleBudget_mono (bits_bound p) (suffix_space p)
  have input := Nat.mul_le_mul_left searchInputCoefficient (Nat.add_le_add_right
    (Nat.add_le_add (suffix_space p) (bits_bound p)) 2)
  simp only [spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,cycleBudgetPolynomial_eval,
    searchBudget] at *
  omega

end LeanTrominoes.PeriodicThreeDM.FieldSavitch
