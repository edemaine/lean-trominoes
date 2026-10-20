/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMDecoderExpressions

/-! # Decoder circuits reading the two original representatives

The slots contain d² row-major basis entries followed by d coordinates for
each representative. The coordinate difference and unit displacement are
computed inside the circuit, so no derived vector is supplied as input.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary.Circuit

def rawBasisIndex (d : ℕ) (i j : Fin d) : Fin (d*d+2*d) :=
  ⟨i.val*d+j.val,(basisIndex d i j).isLt.trans_le (by omega)⟩

def firstOriginIndex (d : ℕ) (i : Fin d) : Fin (d*d+2*d) :=
  ⟨d*d+i.val,by have := i.isLt; omega⟩

def secondOriginIndex (d : ℕ) (i : Fin d) : Fin (d*d+2*d) :=
  ⟨d*d+d+i.val,by have := i.isLt; omega⟩

def rawMatrixExpression (d : ℕ) : Matrix (Fin d) (Fin d) (Expression (d*d+2*d)) :=
  fun i j => .input (rawBasisIndex d i j)

def differenceExpression (d : ℕ) (direction coordinate : Fin d) : Expression (d*d+2*d) :=
  .arithmetic .add
    (.arithmetic .sub (.input (firstOriginIndex d coordinate)) (.input (secondOriginIndex d coordinate)))
    (.constant (decide (coordinate=direction)))

noncomputable def rawDeterminantCircuit (d : ℕ) : Expression (d*d+2*d) :=
  determinantExpression (rawMatrixExpression d)

noncomputable def rawNumeratorCircuit (d : ℕ) (direction coordinate : Fin d) : Expression (d*d+2*d) :=
  numeratorExpression (rawMatrixExpression d) (differenceExpression d direction) coordinate

theorem differenceExpression_eval {d : ℕ} {R : Type} [Ring R]
    (inputs : Fin (d*d+2*d) → R) (first second : Fin d → R) (direction coordinate : Fin d)
    (firstEntries : ∀ j, inputs (firstOriginIndex d j)=first j)
    (secondEntries : ∀ j, inputs (secondOriginIndex d j)=second j) :
    (differenceExpression d direction coordinate).eval inputs=
      first coordinate-second coordinate+(if coordinate=direction then 1 else 0) := by
  by_cases same : coordinate=direction <;>
    simp [differenceExpression,Expression.eval,Operation.eval,bitValue,firstEntries,secondEntries,same]

theorem rawDeterminantCircuit_eval {d : ℕ} {R : Type} [CommRing R]
    (inputs : Fin (d*d+2*d) → R) (A : Matrix (Fin d) (Fin d) R)
    (entries : ∀ i j, inputs (rawBasisIndex d i j)=A i j) :
    (rawDeterminantCircuit d).eval inputs=A.det := by
  rw [rawDeterminantCircuit,eval_determinantExpression]
  congr 1
  funext i j
  exact entries i j

theorem rawNumeratorCircuit_eval {d : ℕ} {R : Type} [CommRing R]
    (inputs : Fin (d*d+2*d) → R) (A : Matrix (Fin d) (Fin d) R)
    (first second : Fin d → R) (direction coordinate : Fin d)
    (entries : ∀ i j, inputs (rawBasisIndex d i j)=A i j)
    (firstEntries : ∀ j, inputs (firstOriginIndex d j)=first j)
    (secondEntries : ∀ j, inputs (secondOriginIndex d j)=second j) :
    (rawNumeratorCircuit d direction coordinate).eval inputs=
      A.adjugate.mulVec (fun j => first j-second j+(if j=direction then 1 else 0)) coordinate := by
  rw [rawNumeratorCircuit,eval_numeratorExpression]
  have matrixEq : (fun a b => (rawMatrixExpression d a b).eval inputs : Matrix (Fin d) (Fin d) R)=A := by
    funext a b
    exact entries a b
  have vectorEq : (fun j => (differenceExpression d direction j).eval inputs)=
      (fun j => first j-second j+(if j=direction then 1 else 0)) := by
    funext j
    exact differenceExpression_eval inputs first second direction j firstEntries secondEntries
  rw [matrixEq,vectorEq]

end LeanTrominoes.Domino.WordRAM.Binary.Circuit
