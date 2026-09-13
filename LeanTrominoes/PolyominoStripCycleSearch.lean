/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCyclePair
import LeanTrominoes.PartrecBoundedAnySpace

/-! # A complete bounded-space cycle search for variable strip tiles -/

namespace LeanTrominoes.PolyominoStripWindow.Savitch
open Turing Turing.ToPartrec Turing.PartrecToTM2 Turing.PartrecToTM2.EvaluatorCodeFits FiniteState
open BoundedArithmetic

def cycleValues (bits : Nat) (rest : List Nat) : List Nat := [2^bits,bits] ++ rest

def outerValues (bits first : Nat) (rest : List Nat) : List Nat := first :: cycleValues bits rest

def prependFieldCode (index : Nat) : Code := Code.prepend (Code.get index) Code.id
def prependFieldCoefficient (index : Nat) : Nat := 4*(10000*(index+1)+10+1)

def outerCode : Code := (Code.boundedAnyCode pairCode).comp (prependFieldCode 1)
def cycleCode : Code := (Code.boundedAnyCode outerCode).comp (prependFieldCode 0)

def outerPredicate (cells : Bool → List Cell) (height bound bits first : Nat) : Bool :=
  boundedAny (pairPredicate cells height bound bits first) (2^bits)

def cyclePredicate (cells : Bool → List Cell) (height bound bits : Nat) : Bool :=
  boundedAny (outerPredicate cells height bound bits) (2^bits)

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

theorem outer_eval (cells : Bool → List Cell) (height bound bits first : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    outerCode.eval (outerValues bits first (suffix cells height bound)) =
      pure [(outerPredicate cells height bound bits first).toNat] := by
  have run := Code.boundedAnyCode_eval pairCode (outerValues bits first (suffix cells height bound))
    (pairPredicate cells height bound bits first)
    (fun second => pair_eval cells height bound bits first second bounded) (2^bits)
  have prep : (prependFieldCode 1).eval (outerValues bits first (suffix cells height bound)) =
      pure (2^bits :: outerValues bits first (suffix cells height bound)) := by
    simp [prependFieldCode,outerValues,cycleValues]
  simpa [outerCode,prep,outerPredicate,Part.bind_eq_bind] using run

theorem cycle_eval_guarded (cells : Bool → List Cell) (height bound bits : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    cycleCode.eval (cycleValues bits (suffix cells height bound)) =
      pure [(cyclePredicate cells height bound bits).toNat] := by
  have run := Code.boundedAnyCode_eval outerCode (cycleValues bits (suffix cells height bound))
    (outerPredicate cells height bound bits) (fun first => outer_eval cells height bound bits first bounded) (2^bits)
  have prep : (prependFieldCode 0).eval (cycleValues bits (suffix cells height bound)) =
      pure (2^bits :: cycleValues bits (suffix cells height bound)) := by simp [prependFieldCode,cycleValues]
  simpa [cycleCode,prep,cyclePredicate,Part.bind_eq_bind] using run

private theorem boundedAny_congr (p q : Nat → Bool) (count : Nat) (h : ∀ i < count, p i = q i) :
    boundedAny p count = boundedAny q count := by
  induction count with
  | zero => rfl
  | succ n ih =>
    rw [boundedAny,boundedAny,h n (by omega),ih (fun i hi => h i (by omega))]

theorem cyclePredicate_eq (cells : Bool → List Cell) (height bound bits : Nat) :
    cyclePredicate cells height bound bits = cycleSearchIndexDFSBoolAtDepth (2^bits) bits (Raw.check cells height bound) := by
  unfold cyclePredicate outerPredicate cycleSearchIndexDFSBoolAtDepth
  apply boundedAny_congr
  intro first hf
  apply boundedAny_congr
  intro second hs
  simp [pairPredicate,hf,hs]

theorem cycle_eval (cells : Bool → List Cell) (height bound bits : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    cycleCode.eval (cycleValues bits (suffix cells height bound)) =
      pure [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (Raw.check cells height bound)).toNat] := by
  rw [cycle_eval_guarded cells height bound bits bounded,cyclePredicate_eq]

def innerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (pairBudget bits space)
def outerBudget (bits space : Nat) : Nat := innerAnyBudget bits space+prependFieldCoefficient 1*(requestBudget bits space+1)
def outerAnyBudget (bits space : Nat) : Nat := boundedAnyBudget (requestBudget bits space) (bits+1) (outerBudget bits space)
def cycleBudget (bits space : Nat) : Nat := outerAnyBudget bits space+prependFieldCoefficient 0*(requestBudget bits space+1)

theorem outer_fits (cells : Bool → List Cell) (height bound bits first : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) (hf : first ≤ 2^bits) :
    EvaluatorCodeFits outerCode (outerValues bits first (suffix cells height bound))
      [(outerPredicate cells height bound bits first).toNat]
      (outerBudget bits (encodedListSpace (suffix cells height bound))) := by
  let values := outerValues bits first (suffix cells height bound)
  let space := encodedListSpace (suffix cells height bound)
  have hv : encodedListSpace values ≤ requestBudget bits space := outer_space_le bits first _ hf
  have inner := boundedAny_uniform pairCode values (pairPredicate cells height bound bits first)
    (2^bits) (bits+1) (pairBudget bits space) (counter_length_le bits)
    (fun second hs => pair_fits cells height bound bits first second bounded hf hs)
  have inner' : EvaluatorCodeFits (Code.boundedAnyCode pairCode) (2^bits :: values)
      [(outerPredicate cells height bound bits first).toNat] (innerAnyBudget bits space) := by
    apply inner.mono
    unfold innerAnyBudget boundedAnyBudget
    omega
  have prep := prependField_fits 1 values
  have prep' : EvaluatorCodeFits (prependFieldCode 1) values (2^bits :: values)
      (prependFieldCoefficient 1*(requestBudget bits space+1)) :=
    prep.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right hv 1))
  exact comp inner' prep'

theorem cycle_fits (cells : Bool → List Cell) (height bound bits : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    EvaluatorCodeFits cycleCode (cycleValues bits (suffix cells height bound))
      [(cycleSearchIndexDFSBoolAtDepth (2^bits) bits (Raw.check cells height bound)).toNat]
      (cycleBudget bits (encodedListSpace (suffix cells height bound))) := by
  let values := cycleValues bits (suffix cells height bound)
  let space := encodedListSpace (suffix cells height bound)
  have hv : encodedListSpace values ≤ requestBudget bits space := cycle_space_le bits _
  have outer := boundedAny_uniform outerCode values (outerPredicate cells height bound bits)
    (2^bits) (bits+1) (outerBudget bits space) (counter_length_le bits)
    (fun first hf => outer_fits cells height bound bits first bounded hf)
  have outer' : EvaluatorCodeFits (Code.boundedAnyCode outerCode) (2^bits :: values)
      [(cyclePredicate cells height bound bits).toNat] (outerAnyBudget bits space) := by
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

end LeanTrominoes.PolyominoStripWindow.Savitch
