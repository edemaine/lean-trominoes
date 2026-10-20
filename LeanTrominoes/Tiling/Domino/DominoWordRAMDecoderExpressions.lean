/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDeterminantExpressions
import LeanTrominoes.Tiling.Domino.DominoWordRAMIntegerExpressions

/-! # Fixed-dimension decoder expressions over original entry arrays

The first d² input slots are the basis matrix in row order. The next d slots
are the difference vector being tested. Every remaining slot is circuit work
memory, independent of the number of representatives in the input region.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit

/-- Row-major input position of a basis entry. -/
def basisIndex (d : ℕ) (i j : Fin d) : Fin (d*d+d) :=
  ⟨i.val*d+j.val,by
    have row := Nat.mul_le_mul_right d (show i.val+1≤d by omega)
    have col := j.isLt
    nlinarith⟩

/-- Difference-vector inputs follow the basis matrix. -/
def vectorIndex (d : ℕ) (i : Fin d) : Fin (d*d+d) := ⟨d*d+i.val,by have := i.isLt; omega⟩

def matrixExpression (d : ℕ) : Matrix (Fin d) (Fin d) (Expression (d*d+d)) :=
  fun i j => .input (basisIndex d i j)

def vectorExpression (d : ℕ) : Fin d → Expression (d*d+d) :=
  fun i => .input (vectorIndex d i)

noncomputable def determinantCircuit (d : ℕ) : Expression (d*d+d) :=
  determinantExpression (matrixExpression d)

noncomputable def numeratorCircuit (d : ℕ) (i : Fin d) : Expression (d*d+d) :=
  numeratorExpression (matrixExpression d) (vectorExpression d) i

/-- Only original basis entries occur in the determinant computation. -/
theorem determinantCircuit_eval {d : ℕ} {R : Type} [CommRing R]
    (inputs : Fin (d*d+d) → R) (A : Matrix (Fin d) (Fin d) R)
    (entries : ∀ i j, inputs (basisIndex d i j)=A i j) :
    (determinantCircuit d).eval inputs=A.det := by
  rw [determinantCircuit,eval_determinantExpression]
  congr 1
  funext i j
  exact entries i j

/-- The numerator computation uses the same basis entries and the raw
coordinate difference, with no supplied inverse or decoded coordinate. -/
theorem numeratorCircuit_eval {d : ℕ} {R : Type} [CommRing R]
    (inputs : Fin (d*d+d) → R) (A : Matrix (Fin d) (Fin d) R) (x : Fin d → R) (i : Fin d)
    (entries : ∀ a b, inputs (basisIndex d a b)=A a b)
    (coordinates : ∀ j, inputs (vectorIndex d j)=x j) :
    (numeratorCircuit d i).eval inputs=A.adjugate.mulVec x i := by
  rw [numeratorCircuit,eval_numeratorExpression]
  have matrixEq : (fun a b => (matrixExpression d a b).eval inputs : Matrix (Fin d) (Fin d) R)=A := by
    funext a b
    exact entries a b
  have vectorEq : (fun j => (vectorExpression d j).eval inputs)=x := by
    funext j
    exact coordinates j
  rw [matrixEq,vectorEq]

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
