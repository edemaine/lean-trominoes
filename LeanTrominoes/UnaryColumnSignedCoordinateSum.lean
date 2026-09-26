/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnSignedFloorDivision
import LeanTrominoes.UnaryColumnSignedRemainder
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # Quotients and remainders of sums of signed coordinate columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing SignedUnaryCoordinateRefinement
variable {Symbol Row : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Row} {a b : List Symbol → Row → Int} {d : List Symbol → Nat}
  (ap : Compiler rows (fun s r => field true (a s r)))
  (an : Compiler rows (fun s r => field false (a s r)))
  (bp : Compiler rows (fun s r => field true (b s r)))
  (bn : Compiler rows (fun s r => field false (b s r)))
  (cd : ScalarCompiler d) (positive : ∀ s, 0 < d s)

private theorem sum_signed (a b : Int) :
    ((field true a + field true b : Nat) : Int) - (field false a + field false b : Nat) = a+b := by
  simp only [field,Nat.cast_add,Bool.false_eq_true,↓reduceIte]
  omega

def signedSumQuotient : Compiler rows (fun s r => Encodable.encode ((a s r+b s r)/(d s:Int))) := by
  apply TM2ComputableInPolyTime.of_eq (signedFloorDivide (add ap bp) (add an bn) cd positive)
  intro s
  apply List.map_congr_left
  intro r _
  change Encodable.encode (((((field true (a s r) + field true (b s r) : Nat) : Int) -
    (field false (a s r) + field false (b s r) : Nat))) / (d s:Int)) = _
  rw [sum_signed]

def signedSumRemainder : Compiler rows (fun s r => ((a s r+b s r)%(d s:Int)).toNat) := by
  apply TM2ComputableInPolyTime.of_eq (signedRemainder (add ap bp) (add an bn) cd positive)
  intro s
  apply List.map_congr_left
  intro r _
  change (((((field true (a s r) + field true (b s r) : Nat) : Int) -
    (field false (a s r) + field false (b s r) : Nat)) % (d s:Int)).toNat) = _
  rw [sum_signed]

end LeanTrominoes.UnaryColumn
end
