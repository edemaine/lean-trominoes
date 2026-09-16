/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionStripEncoding
import LeanTrominoes.PolyominoStripArithmeticGeometry

/-! # Bounded natural coordinates for the strip completion checker -/
namespace LeanTrominoes.PeriodicStripTrominoPrefill.Raw
open PolyominoStripWindow.Arithmetic

/-- The sum of unary fields bounds every signed input coordinate. -/
def bound (input : PeriodicStripTrominoPrefill) : Nat :=
  3 + (CompletionStripEncoding.fields input).sum

def fields (input : PeriodicStripTrominoPrefill) : List Nat :=
  bound input :: CompletionStripEncoding.fields input

def sourceCell (t : Tromino) (k : Fin 3) : Cell :=
  match t with
  | .I => (k.val,0)
  | .L => (if k.val = 1 then 1 else 0,if k.val = 2 then 1 else 0)

theorem cells_eq_source (t : Tromino) : t.cells = Finset.univ.image (sourceCell t) := by
  cases t <;> decide +kernel

theorem source_mem (t : Tromino) (k : Fin 3) : sourceCell t k ∈ t.cells := by
  rw [cells_eq_source]
  exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩

theorem source_act_bounds (t : Tromino) (s : SquareSymmetry) (k : Fin 3) :
    -2 ≤ (s.act (sourceCell t k)).1 ∧ (s.act (sourceCell t k)).1 ≤ 2 ∧
    -2 ≤ (s.act (sourceCell t k)).2 ∧ (s.act (sourceCell t k)).2 ≤ 2 := by
  revert t s k
  decide +kernel

private theorem member_le_sum {xs : List Nat} {a : Nat} (ha : a ∈ xs) : a ≤ xs.sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha
      omega

private theorem int_code_bounds (z : Int) :
    -(Encodable.encode z : Int) ≤ z ∧ z ≤ Encodable.encode z := by
  cases z with
  | ofNat n => change -(2*n : Nat) ≤ (n : Int) ∧ (n : Int) ≤ (2*n : Nat); omega
  | negSucc n => change -(2*n+1 : Nat) ≤ Int.negSucc n ∧ Int.negSucc n ≤ (2*n+1 : Nat); omega

theorem offset_bounds (input : PeriodicStripTrominoPrefill) (p : Placement Unit) (hp : p ∈ input.motif) :
    -(bound input : Int)+3 ≤ p.offset.1 ∧ p.offset.1 ≤ (bound input : Int)-3 ∧
    -(bound input : Int)+3 ≤ p.offset.2 ∧ p.offset.2 ≤ (bound input : Int)-3 := by
  have members : ∀ v ∈ CompletionStripEncoding.placementFields p,
      v ∈ CompletionStripEncoding.fields input := by
    intro v hv
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨p,hp,hv⟩))
  have hx := member_le_sum (members (Encodable.encode p.offset.1) (by simp [CompletionStripEncoding.placementFields]))
  have hy := member_le_sum (members (Encodable.encode p.offset.2) (by simp [CompletionStripEncoding.placementFields]))
  have bx := int_code_bounds p.offset.1
  have by' := int_code_bounds p.offset.2
  dsimp [bound]
  omega

def biasedCell (t : Tromino) (b : Nat) (p : Placement Unit) (k : Fin 3) : Nat × Nat :=
  (bias b (Encodable.encode p.offset.1) +
      bias 2 (orientedX (CompletionStripEncoding.symmetryCode p.symmetry)
        (Encodable.encode (sourceCell t k).1) (Encodable.encode (sourceCell t k).2)) - 2,
   bias b (Encodable.encode p.offset.2) +
      bias 2 (orientedY (CompletionStripEncoding.symmetryCode p.symmetry)
        (Encodable.encode (sourceCell t k).1) (Encodable.encode (sourceCell t k).2)) - 2)

theorem symmetryCode_eq (s : SquareSymmetry) :
    CompletionStripEncoding.symmetryCode s = PolyominoStripWindow.Raw.symmetryIndex s := by
  cases s <;> rfl

theorem biasedCell_eq (t : Tromino) (input : PeriodicStripTrominoPrefill)
    (p : Placement Unit) (hp : p ∈ input.motif) (k : Fin 3) :
    ((biasedCell t (bound input) p k).1 : Int) = (bound input : Int)+(p.offset.1+(p.symmetry.act (sourceCell t k)).1) ∧
    ((biasedCell t (bound input) p k).2 : Int) = (bound input : Int)+(p.offset.2+(p.symmetry.act (sourceCell t k)).2) := by
  have hb := offset_bounds input p hp
  have hs := source_act_bounds t p.symmetry k
  have ox := bias_encode (bound input) p.offset.1 (by omega)
  have oy := bias_encode (bound input) p.offset.2 (by omega)
  have sx := bias_encode 2 (p.symmetry.act (sourceCell t k)).1 hs.1
  have sy := bias_encode 2 (p.symmetry.act (sourceCell t k)).2 hs.2.2.1
  simp only [biasedCell,symmetryCode_eq,orientedX_encode,orientedY_encode]
  omega

theorem bound_le_length (input : PeriodicStripTrominoPrefill) :
    bound input ≤ (CompletionStripEncoding.finEncoding.encode input).length+3 := by
  simp only [CompletionStripEncoding.finEncoding,CompletionStripEncoding.unaryFields_length,bound]
  omega

end LeanTrominoes.PeriodicStripTrominoPrefill.Raw
