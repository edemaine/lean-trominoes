/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripCoverageExpr

/-! # A bounded arithmetic formula for the complete strip transition -/

namespace LeanTrominoes.PolyominoStripWindow.Formula
open BoundedArithmetic BoundedArithmetic.Expr
set_option maxHeartbeats 200000

def equalCandidates : Expr :=
  andE (eqE (var 0) (var 4)) (andE (eqE (var 1) (var 5))
    (andE (eqE (var 2) (var 6)) (eqE (var 3) (var 7))))

def firstColumn : Expr :=
  forallCandidates 0 (impE (eqE (var 3) 0) (impE (selected 4 false 0) (fitsAt 4)))

def coverageRow : Expr :=
  existsCandidates 1 (andE (coversAt 5 4)
    (forallCandidates 5 (impE (coversAt 9 8) equalCandidates)))

def coverage : Expr := .all (var 0) coverageRow

def overlapBits : Expr :=
  andE (impE (selected 4 false 1) (selected 4 true 0))
    (impE (selected 4 true 0) (selected 4 false 1))

def overlap : Expr :=
  forallCandidates 0 (impE (ltE (var 3) (2*var 5)) overlapBits)

def transition : Expr := andE firstColumn (andE coverage overlap)

theorem equalCandidates_truth (a b : Raw.Candidate) (rest : List Nat) :
    equalCandidates.Truth (Arithmetic.candidateFields b ++ (Arithmetic.candidateFields a ++ rest)) ↔ b = a := by
  rw [← Arithmetic.candidateFields_injective.eq_iff]
  simp [equalCandidates,truth_and,truth_eq,eval_var,Arithmetic.candidateFields]

theorem firstColumn_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    firstColumn.Truth (Arithmetic.input cells height bound first second) ↔
      ∀ slot ∈ Raw.slots height bound,
        Raw.selected height bound first (0,slot) = true → Raw.Fits cells height bound slot := by
  rw [firstColumn]
  rw [show 0 = ([] : List Nat).length from rfl]
  rw [show Arithmetic.input cells height bound first second = [] ++ Arithmetic.input cells height bound first second from rfl]
  rw [forallCandidates_truth]
  have leaf (a : Raw.Candidate) (ha : a ∈ Raw.keys height bound) :
      (impE (eqE (var 3) 0) (impE (selected 4 false 0) (fitsAt 4))).Truth
        (Arithmetic.candidateFields a ++ ([] ++ Arithmetic.input cells height bound first second)) ↔
      (a.1 = 0 → Raw.selected height bound first a = true → Raw.Fits cells height bound a.2) := by
    have sf := selected_truth cells height bound first second [] a false 0
    have ff := fitsAt_truth cells height bound first second bounded [] a
    simp only [List.length_nil,Nat.reduceAdd] at sf ff
    rw [truth_imp,truth_eq,truth_imp,sf,ff]
    simp [eval_var,Arithmetic.candidateFields,Expr.eval,
      Raw.selected_eq_testBit_address height bound first a ha]
  simp only [List.length_nil]
  conv_lhs => intro a ha; rw [leaf a ha]
  constructor
  · intro h slot hs bit
    exact h (0,slot) ((Raw.mem_keys _).mpr ⟨by omega,(Raw.mem_slots _).mp hs⟩) rfl bit
  · intro h a ha hc bit
    have hs := (Raw.mem_slots a.2).mpr ((Raw.mem_keys a).mp ha).2
    have eq : a = (0,a.2) := Prod.ext hc rfl
    exact h a.2 hs (by rw [eq] at bit; exact bit)

theorem coverageRow_truth (cells : Bool → List Cell) (height bound first second row : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    coverageRow.Truth (row :: Arithmetic.input cells height bound first second) ↔
      ∃ a ∈ Raw.keys height bound, Raw.Covers cells height bound first row a ∧
        ∀ b ∈ Raw.keys height bound, Raw.Covers cells height bound first row b → b = a := by
  change (existsCandidates [row].length _).Truth ([row] ++ Arithmetic.input cells height bound first second) ↔ _
  rw [existsCandidates_truth]
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  rw [truth_and]
  have ca := coversAt_truth cells height bound first second bounded [row] a 4 ha
  change (coversAt 5 4).Truth
    (Arithmetic.candidateFields a ++ ([row] ++ Arithmetic.input cells height bound first second)) ↔
    Raw.Covers cells height bound first row a at ca
  rw [ca]
  apply and_congr Iff.rfl
  change (forallCandidates (Arithmetic.candidateFields a ++ [row]).length _).Truth
    ((Arithmetic.candidateFields a ++ [row]) ++ Arithmetic.input cells height bound first second) ↔ _
  rw [forallCandidates_truth]
  apply forall_congr'
  intro b
  apply imp_congr_right
  intro hb
  rw [truth_imp]
  have cb := coversAt_truth cells height bound first second bounded (Arithmetic.candidateFields a ++ [row]) b 8 hb
  have eq := equalCandidates_truth a b (row :: Arithmetic.input cells height bound first second)
  simpa [Arithmetic.candidateFields] using imp_congr cb eq

theorem coverage_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    coverage.Truth (Arithmetic.input cells height bound first second) ↔
      ∀ row ∈ List.range height, ∃ a ∈ Raw.keys height bound,
        Raw.Covers cells height bound first row a ∧
          ∀ b ∈ Raw.keys height bound, Raw.Covers cells height bound first row b → b = a := by
  rw [coverage,truth_all]
  have hh : (var 0).eval (Arithmetic.input cells height bound first second) = height := rfl
  rw [hh]
  simp only [List.mem_range,coverageRow_truth cells height bound first second _ bounded]

theorem overlapBits_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (a : Raw.Candidate) :
    overlapBits.Truth (Arithmetic.candidateFields a ++ Arithmetic.input cells height bound first second) ↔
      first.testBit (Raw.address height bound (a.1+1,a.2)) =
        second.testBit (Raw.address height bound a) := by
  simp only [overlapBits,truth_and,truth_imp]
  have sf := selected_truth cells height bound first second [] a false 1
  have sg := selected_truth cells height bound first second [] a true 0
  simp only [List.length_nil,Nat.reduceAdd,List.nil_append] at sf sg
  rw [sf,sg]
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,Prod.eta]
  cases first.testBit (Raw.address height bound (a.1+1,a.2)) <;>
    cases second.testBit (Raw.address height bound a) <;> simp

theorem overlap_truth (cells : Bool → List Cell) (height bound first second : Nat) :
    overlap.Truth (Arithmetic.input cells height bound first second) ↔
      ∀ column ∈ List.range (2*bound), ∀ slot ∈ Raw.slots height bound,
        Raw.selected height bound first (column+1,slot) = Raw.selected height bound second (column,slot) := by
  have quant := forallCandidates_truth cells height bound first second []
    (impE (ltE (var 3) (2*var 5)) overlapBits)
  simp only [List.length_nil,List.nil_append] at quant
  rw [overlap,quant]
  have leaf (a : Raw.Candidate) :
      (impE (ltE (var 3) (2*var 5)) overlapBits).Truth
        (Arithmetic.candidateFields a ++ ([] ++ Arithmetic.input cells height bound first second)) ↔
      (a.1 < 2*bound → first.testBit (Raw.address height bound (a.1+1,a.2)) =
        second.testBit (Raw.address height bound a)) := by
    simp only [List.nil_append]
    rw [truth_imp,truth_lt,overlapBits_truth]
    rfl
  simp only [List.nil_append] at leaf
  simp_rw [leaf]
  constructor
  · intro h column hc slot hs
    have hc' := List.mem_range.mp hc
    have hs' := (Raw.mem_slots slot).mp hs
    rw [Raw.selected_eq_testBit_address _ _ _ _ ((Raw.mem_keys _).mpr ⟨by omega,hs'⟩),
      Raw.selected_eq_testBit_address _ _ _ _ ((Raw.mem_keys _).mpr ⟨by omega,hs'⟩)]
    exact h (column,slot) ((Raw.mem_keys _).mpr ⟨by omega,hs'⟩) hc'
  · intro h a ha hc
    have hs := (Raw.mem_slots a.2).mpr ((Raw.mem_keys a).mp ha).2
    have h' := h a.1 (List.mem_range.mpr hc) a.2 hs
    rw [Raw.selected_eq_testBit_address height bound first (a.1+1,a.2)
        ((Raw.mem_keys _).mpr ⟨by omega,(Raw.mem_slots _).mp hs⟩),
      Raw.selected_eq_testBit_address height bound second a ha] at h'
    exact h'

theorem transition_truth (cells : Bool → List Cell) (height bound first second : Nat)
    (bounded : Bounded (Raw.tiles cells) bound) :
    transition.Truth (Arithmetic.input cells height bound first second) ↔
      Raw.Transition cells height bound first second := by
  rw [transition,truth_and,truth_and,firstColumn_truth _ _ _ _ _ bounded,
    coverage_truth _ _ _ _ _ bounded,overlap_truth]
  rfl

theorem transition_noPower : transition.noPower = true := by
  simp [transition,firstColumn,coverage,coverageRow,overlap,overlapBits,equalCandidates,
    andE,impE,eqE,ltE,Expr.noPower,forallCandidates_noPower,existsCandidates_noPower,
    selected_noPower,fitsAt_noPower,coversAt_noPower]

end LeanTrominoes.PolyominoStripWindow.Formula
