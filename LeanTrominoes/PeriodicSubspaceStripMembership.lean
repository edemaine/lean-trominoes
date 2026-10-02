/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripSavitch

/-! # Lemma 5.1: native binary PSPACE membership for arbitrary strip footprints

The palette, target subspace, and prescribed placement orbits are all input.
For each fixed polynomial bounding box this constructs a finite-alphabet
Turing-machine decider and bounds every reachable configuration's space.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldSavitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits
open Polynomial BoundedArithmetic

def suffixCode : Code := Code.prepend (Code.get 0) (Code.prepend (Code.get 1)
  (Code.prepend (Code.get 2) (Code.prepend Code.zero (Code.prepend Code.zero (Code.drop 3)))))
def suffixCoefficient : Nat :=
  4*(10000+4*(20000+4*(30000+4*(10000+4*(10000+40000+1)+1)+1)+1)+1)

theorem suffixCode_eval (f : Input) : suffixCode.eval (Encoding.fields f)=pure (suffix f) := by
  simp [suffixCode,Encoding.fields,Part.bind_eq_bind,suffix,FieldPredicate.input,FieldPredicate.context]

theorem suffixCode_fits (f : Input) :
    EvaluatorCodeFits suffixCode (Encoding.fields f) (suffix f)
      (suffixCoefficient*((Encoding.finEncoding.encode f).length+1)) := by
  let values := Encoding.fields f
  have z := zero_unit values (encodedListSpace values+1) le_rfl
  have fit := prepend_linear (get_linear 0 values) (prepend_linear (get_linear 1 values)
    (prepend_linear (get_linear 2 values) (prepend_linear z (prepend_linear z (drop_linear 3 values)))))
  change EvaluatorCodeFits suffixCode values (suffix f) (suffixCoefficient*(encodedListSpace values+1)) at fit
  simpa only [values,Encoding.fields_space] using fit

theorem suffix_space (f : Input) : encodedListSpace (suffix f)=(Encoding.finEncoding.encode f).length+2 := by
  rw [← Encoding.fields_space]
  have zeroLength : (_root_.Computability.encodeNat 0).length=0 := rfl
  simp only [suffix,FieldPredicate.input,FieldPredicate.context,Encoding.fields,List.cons_append,List.nil_append,
    encodedListSpace_cons,zeroLength]
  omega

def decideCode : Code := searchCode.comp suffixCode

theorem decide_eval (f : Input) : decideCode.eval (Encoding.fields f)=pure [(result f).toNat] := by
  simp [decideCode,suffixCode_eval,search_eval,Part.bind_eq_bind]

noncomputable def bitPolynomial (p : Polynomial Nat) : Polynomial Nat := (2*p+1)*X
noncomputable def spacePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  cycleBudgetPolynomial (bitPolynomial p) (X+2)+
    C searchInputCoefficient*(X+2+bitPolynomial p+2)+C suffixCoefficient*(X+1)

theorem bits_bound (p : Polynomial Nat) (f : PolynomialBoxInput p) :
    bits f.val ≤ (bitPolynomial p).eval (Encoding.finEncoding.encode f.val).length := by
  have bound := f.property
  have rows := Encoding.records_le_length f.val
  simp only [PolynomialBox] at bound
  simp only [bitPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_ofNat,
    Polynomial.eval_one,Polynomial.eval_X]
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bound) 1) rows

theorem decide_fits (p : Polynomial Nat) (f : PolynomialBoxInput p) :
    EvaluatorCodeFits decideCode (Encoding.fields f.val) [(result f.val).toNat]
      ((spacePolynomial p).eval (Encoding.finEncoding.encode f.val).length) := by
  have fit := EvaluatorCodeFits.comp (search_fits f.val) (suffixCode_fits f.val)
  apply fit.mono
  have cycle := cycleBudget_mono (bits_bound p f) (Nat.le_of_eq (suffix_space f.val))
  have linear := Nat.mul_le_mul_left searchInputCoefficient
    (show encodedListSpace (suffix f.val)+bits f.val+2 ≤
      (Encoding.finEncoding.encode f.val).length+2+(bitPolynomial p).eval (Encoding.finEncoding.encode f.val).length+2 by
      rw [suffix_space]; exact Nat.add_le_add_left (Nat.add_le_add_right (bits_bound p f) 2) _)
  simp only [spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,cycleBudgetPolynomial_eval]
  unfold searchBudget
  omega

theorem run_fits (p : Polynomial Nat) (f : PolynomialBoxInput p) :
    EvaluatorRunFits decideCode (PolynomialBoxEncoding.fields p f)
      ((spacePolynomial p).eval ((PolynomialBoxEncoding.finEncoding p).encode f).length) := by
  let fit := decide_fits p f
  let after := EvaluatorExecutionFits.ret_halt fit.output_space
  apply EvaluatorRunFits.of_call
  exact fit.call .halt _ (by simp [continuationSpace,trContStack]) after

noncomputable def decider (p : Polynomial Nat) :
    Complexity.DeciderInPolySpace (PolynomialBoxEncoding.finEncoding p) (fun f => Problem f.val) := by
  exact deciderInPolySpace_of_flatEvaluatorRunFits (PolynomialBoxEncoding.fields p)
    (PolynomialBoxEncoding.decode p) (PolynomialBoxEncoding.decode_fields p)
    decideCode (fun f => result f.val) (fun f => result_correct f.val)
    (fun f => by unfold PolynomialBoxEncoding.fields; rw [decide_eval]; apply Part.mem_some_iff.mpr; cases result f.val <;> rfl)
    (spacePolynomial p) (run_fits p)

end LeanTrominoes.PeriodicSubspaceTiling.Strip.FieldSavitch
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip

/-- The completion half of Lemma 5.1, with arbitrary finite footprints and
any fixed polynomial bounding box under native binary encoding. -/
theorem completion_inPSPACE (p : Polynomial Nat) :
    Complexity.InPSPACE (PolynomialBoxEncoding.finEncoding p) (fun f => Problem f.val) :=
  ⟨FieldSavitch.decider p⟩

end LeanTrominoes.PeriodicSubspaceTiling.Strip
