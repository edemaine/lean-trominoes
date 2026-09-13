/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripEncoding
import LeanTrominoes.PolyominoStripWindowSearch
import LeanTrominoes.PolyominoConnectivitySearch

/-! # A verified decision procedure for the two-polyomino strip predicate -/

namespace LeanTrominoes.Theorem55StripDecider

/-- The sum of the unary fields bounds every coordinate magnitude. -/
def bound (input : Theorem55.StripInput) : Nat := 7 + (Theorem55StripEncoding.fields input).sum

private theorem member_le_sum {values : List Nat} {v : Nat} (member : v ∈ values) : v ≤ values.sum := by
  induction values with
  | nil => simp at member
  | cons a rest ih =>
    simp only [List.mem_cons] at member
    simp only [List.sum_cons]
    rcases member with rfl | member
    · omega
    · have := ih member
      omega

private theorem int_code_bounds (z : Int) :
    -(Encodable.encode z : Int) ≤ z ∧ z ≤ Encodable.encode z := by
  cases z with
  | ofNat k =>
    rw [Computability.encode_int_ofNat]
    change -(2*k : Nat) ≤ (k : Int) ∧ (k : Int) ≤ (2*k : Nat)
    omega
  | negSucc k =>
    rw [Computability.encode_int_negSucc]
    omega

theorem tiles_bounded (input : Theorem55.StripInput) :
    PolyominoStripWindow.Bounded (pairTiles PlusRefinement.bumpy input.2.toFinset) (bound input) := by
  have small : ∀ c ∈ PlusRefinement.bumpy, -(7 : Int) ≤ c.1 ∧ c.1 ≤ 7 ∧ -(7 : Int) ≤ c.2 ∧ c.2 ≤ 7 := by decide
  intro k c hc
  cases k with
  | false =>
    have h := small c hc
    dsimp [bound]
    omega
  | true =>
    have member : c ∈ input.2 := List.mem_toFinset.mp hc
    have fields : ∀ v ∈ PeriodicStripFlatEncoding.cellFields c, v ∈ Theorem55StripEncoding.fields input := by
      intro v hv
      apply List.mem_append.mpr
      right
      exact List.mem_flatMap.mpr ⟨c,member,hv⟩
    have hx := member_le_sum (fields (Encodable.encode c.1) (by simp [PeriodicStripFlatEncoding.cellFields]))
    have hy := member_le_sum (fields (Encodable.encode c.2) (by simp [PeriodicStripFlatEncoding.cellFields]))
    have xbounds := int_code_bounds c.1
    have ybounds := int_code_bounds c.2
    dsimp [bound]
    omega

/-- The algorithm first rejects invalid shape data, then searches the finite window graph.
No polynomial-workspace machine certificate is asserted by this definition. -/
def decideStrip (input : Theorem55.StripInput) : Bool :=
  decide (0 < input.1) && decide (input.2 ≠ []) &&
    decide (PolyominoConnectivitySearch.Disconnected input.2) &&
      PolyominoStripWindow.tilingCheck (pairTiles PlusRefinement.bumpy input.2.toFinset) input.1 (bound input)

theorem decideStrip_correct (input : Theorem55.StripInput) :
    decideStrip input = true ↔ Theorem55.stripProblem input := by
  rw [decideStrip]
  simp only [Bool.and_eq_true,decide_eq_true_eq,PolyominoStripWindow.tilingCheck_correct (tiles_bounded input)]
  by_cases nonempty : input.2 = []
  · simp [nonempty,Theorem55.stripProblem]
  · rw [PolyominoConnectivitySearch.disconnected_iff _ nonempty]
    simp [Theorem55.stripProblem,nonempty,and_assoc]

end LeanTrominoes.Theorem55StripDecider
