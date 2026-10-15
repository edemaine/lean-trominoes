/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.Encoding.Unary.UnaryColumnSignedEncoding
import LeanTrominoes.SAT.CNF.PeriodicCNFFlatEncoding

/-! # A finite-table compiler for differences of small signed coordinates -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Computability Turing PeriodicCNFFlatEncoding

theorem encode_small_int (z : Int) (small : z.natAbs ≤ 1) : Encodable.encode z < 3 := by
  cases z with
  | ofNat n => change n ≤ 1 at small; change 2*n < 3; omega
  | negSucc n => change n+1 ≤ 1 at small; change 2*n+1 < 3; omega

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {f g : List Symbol → Index → Int}

def boundedSignedDifference
    (first : Compiler rows (fun s i => Encodable.encode (f s i)))
    (second : Compiler rows (fun s i => Encodable.encode (g s i)))
    (firstSmall : ∀ s i, i ∈ rows s → (f s i).natAbs ≤ 1)
    (secondSmall : ∀ s i, i ∈ rows s → (g s i).natAbs ≤ 1) :
    Compiler rows (fun s i => Encodable.encode (f s i-g s i)) := by
  let physical := residue (add (scale first 3) second) 9 (by decide)
    (fun code => Encodable.encode (decodeIntField (code.val/3)-decodeIntField (code.val%3)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro i member
  have a := encode_small_int (f s i) (firstSmall s i member)
  have b := encode_small_int (g s i) (secondSmall s i member)
  have bound : Encodable.encode (f s i)*3+Encodable.encode (g s i) < 9 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  have quotient : (Encodable.encode (f s i)*3+Encodable.encode (g s i))/3 = Encodable.encode (f s i) := by omega
  have remainder : (Encodable.encode (f s i)*3+Encodable.encode (g s i))%3 = Encodable.encode (g s i) := by omega
  simp only [quotient,remainder,decodeIntField_encode]

end LeanTrominoes.UnaryColumn
end
