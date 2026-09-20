/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFFieldCyclePair
import LeanTrominoes.PartrecBoundedAnySpace

/-! # A complete-space cycle search for variable CNF windows -/

namespace LeanTrominoes.PeriodicCNF.FieldSavitch
open PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic

def cycleValues (bits : Nat) (rest : List Nat) : List Nat := [2^bits,bits] ++ rest

def outerValues (bits first : Nat) (rest : List Nat) : List Nat := first :: cycleValues bits rest

def prependFieldCode (index : Nat) : Code := Code.prepend (Code.get index) Code.id
def prependFieldCoefficient (index : Nat) : Nat := 4*(10000*(index+1)+10+1)

def outerCode : Code := (Code.boundedAnyCode pairCode).comp (prependFieldCode 1)
def cycleCode : Code := (Code.boundedAnyCode outerCode).comp (prependFieldCode 0)

def outerPredicate (f : PeriodicCNF Nat) (bits first : Nat) : Bool :=
  boundedAny (pairPredicate f bits first) (2^bits)

def cyclePredicate (f : PeriodicCNF Nat) (bits : Nat) : Bool :=
  boundedAny (outerPredicate f bits) (2^bits)

theorem prependField_fits (index : Nat) (values : List Nat) :
    EvaluatorCodeFits (prependFieldCode index) values ((values[index]?.getD 0) :: values)
      (prependFieldCoefficient index*(encodedListSpace values+1)) := by
  have identity := (EvaluatorCodeFits.id values).mono (idCost_bound values)
  exact prepend_linear (get_linear index values) identity

theorem outer_space_le (bits first : Nat) (rest : List Nat) (hf : first ≤ 2^bits) :
    encodedListSpace (outerValues bits first rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have h := pair_space_le bits first 0 rest hf (by omega)
  change encodedListSpace (0 :: outerValues bits first rest) ≤ _ at h
  simp only [encodedListSpace_cons] at h
  omega

theorem cycle_space_le (bits : Nat) (rest : List Nat) :
    encodedListSpace (cycleValues bits rest) ≤ requestBudget bits (encodedListSpace rest) := by
  have h := outer_space_le bits 0 rest (Nat.zero_le _)
  change encodedListSpace (0 :: cycleValues bits rest) ≤ _ at h
  simp only [encodedListSpace_cons] at h
  omega

theorem counter_length_le (bits : Nat) : (Computability.encodeNat (2^bits)).length ≤ bits+1 :=
  FiniteState.encodeNat_length_le_of_lt_pow _ _ (Nat.pow_lt_pow_right (by omega) (by omega))

theorem outer_eval (f : PeriodicCNF Nat) (bits first : Nat) :
    outerCode.eval (outerValues bits first (suffix f)) =
      pure [(outerPredicate f bits first).toNat] := by
  have run := Code.boundedAnyCode_eval pairCode (outerValues bits first (suffix f))
    (pairPredicate f bits first)
    (fun second => pair_eval f bits first second) (2^bits)
  have prep : (prependFieldCode 1).eval (outerValues bits first (suffix f)) =
      pure (2^bits :: outerValues bits first (suffix f)) := by
    simp [prependFieldCode,outerValues,cycleValues]
  simpa [outerCode,prep,outerPredicate,Part.bind_eq_bind] using run

theorem cycle_eval_guarded (f : PeriodicCNF Nat) (bits : Nat) :
    cycleCode.eval (cycleValues bits (suffix f)) =
      pure [(cyclePredicate f bits).toNat] := by
  have run := Code.boundedAnyCode_eval outerCode (cycleValues bits (suffix f))
    (outerPredicate f bits) (fun first => outer_eval f bits first) (2^bits)
  have prep : (prependFieldCode 0).eval (cycleValues bits (suffix f)) =
      pure (2^bits :: cycleValues bits (suffix f)) := by simp [prependFieldCode,cycleValues]
  simpa [cycleCode,prep,cyclePredicate,Part.bind_eq_bind] using run

private theorem boundedAny_congr (p q : Nat → Bool) (count : Nat) (h : ∀ i < count, p i = q i) :
    boundedAny p count = boundedAny q count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [boundedAny,boundedAny,h n (by omega),ih (fun i hi => h i (by omega))]

theorem cyclePredicate_eq (f : PeriodicCNF Nat) (bits : Nat) :
    cyclePredicate f bits = cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f) := by
  unfold cyclePredicate outerPredicate cycleSearchIndexDFSBoolAtDepth
  apply boundedAny_congr
  intro first hf
  apply boundedAny_congr
  intro second hs
  simp [pairPredicate,hf,hs]

theorem cycle_eval (f : PeriodicCNF Nat) (bits : Nat) :
    cycleCode.eval (cycleValues bits (suffix f)) =
      pure [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f)).toNat] := by
  rw [cycle_eval_guarded f bits,cyclePredicate_eq]

def innerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (pairBudget bits space)
def outerBudget (bits space : Nat) : Nat := innerAnyBudget bits space+prependFieldCoefficient 1*(requestBudget bits space+1)
def outerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (outerBudget bits space)
def cycleBudget (bits space : Nat) : Nat := outerAnyBudget bits space+prependFieldCoefficient 0*(requestBudget bits space+1)

theorem outer_fits (f : PeriodicCNF Nat) (bits first : Nat)
    (hf : first ≤ 2^bits) :
    EvaluatorCodeFits outerCode (outerValues bits first (suffix f))
      [(outerPredicate f bits first).toNat]
      (outerBudget bits (encodedListSpace (suffix f))) := by
  let values := outerValues bits first (suffix f)
  let space := encodedListSpace (suffix f)
  have hv : encodedListSpace values ≤ requestBudget bits space := outer_space_le bits first _ hf
  have inner := boundedAny_uniform pairCode values (pairPredicate f bits first)
    (2^bits) (bits+1) (pairBudget bits space) (counter_length_le bits)
    (fun second hs => pair_fits f bits first second hf hs)
  have inner' : EvaluatorCodeFits (Code.boundedAnyCode pairCode) (2^bits :: values)
      [(outerPredicate f bits first).toNat] (innerAnyBudget bits space) := by
    apply inner.mono
    unfold innerAnyBudget boundedAnyBudget
    omega
  have prep := prependField_fits 1 values
  have prep' : EvaluatorCodeFits (prependFieldCode 1) values (2^bits :: values)
      (prependFieldCoefficient 1*(requestBudget bits space+1)) :=
    prep.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
  exact comp inner' prep'

theorem cycle_fits (f : PeriodicCNF Nat) (bits : Nat) :
    EvaluatorCodeFits cycleCode (cycleValues bits (suffix f))
      [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (FieldPredicate.check f)).toNat]
      (cycleBudget bits (encodedListSpace (suffix f))) := by
  let values := cycleValues bits (suffix f)
  let space := encodedListSpace (suffix f)
  have hv : encodedListSpace values ≤ requestBudget bits space := cycle_space_le bits _
  have outer := boundedAny_uniform outerCode values (outerPredicate f bits)
    (2^bits) (bits+1) (outerBudget bits space) (counter_length_le bits)
    (fun first hf => outer_fits f bits first hf)
  have outer' : EvaluatorCodeFits (Code.boundedAnyCode outerCode) (2^bits :: values)
      [(cyclePredicate f bits).toNat] (outerAnyBudget bits space) := by
    apply outer.mono
    unfold outerAnyBudget boundedAnyBudget
    omega
  have prep := prependField_fits 0 values
  have prep' : EvaluatorCodeFits (prependFieldCode 0) values (2^bits :: values)
      (prependFieldCoefficient 0*(requestBudget bits space+1)) :=
    prep.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
  have fit := comp outer' prep'
  rw [cyclePredicate_eq] at fit
  exact fit

end LeanTrominoes.PeriodicCNF.FieldSavitch
