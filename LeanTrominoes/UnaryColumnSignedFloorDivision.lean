/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnDivisionCompiler

/-! # Native signed fields for integer floor division by a positive period -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing

theorem signed_floor_quotient (p n d : Nat) (hd : 0 < d) :
    (((p-n)/d:Nat):Int) - (((n-p+(d-1))/d:Nat):Int) = ((p:Int)-n)/(d:Int) := by
  generalize eq : (p:Int)-n = z
  cases z with
  | ofNat k =>
    have he : (p:Int)-n = (k:Int) := eq
    have hp : p-n = k := by omega
    have hn : n-p = 0 := by omega
    have small : (d-1)/d = 0 := Nat.div_eq_of_lt (by omega)
    simp [hp,hn,small]
  | negSucc k =>
    have hp : p-n = 0 := by omega
    have hn : n-p = k+1 := by omega
    have sum : k+1+(d-1) = k+d := by omega
    rw [hp,hn,sum,Int.negSucc_ediv k (by exact_mod_cast hd)]
    simp [Nat.add_div_right,hd]
    rfl

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {p n : List Symbol → Index → Nat}
  {divisor : List Symbol → Nat}

def signedFloorDivide (cp : Compiler rows p) (cn : Compiler rows n)
    (cd : ScalarCompiler divisor) (positive : ∀ s, 0 < divisor s) :
    Compiler rows (fun s i => Encodable.encode (((p s i:Int)-n s i)/(divisor s:Int))) := by
  let adjustment := sub (broadcast cp cd) (constant cp 1)
  let physical := signedDifference (divide (sub cp cn) cd positive)
    (divide (add (sub cn cp) adjustment) cd positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro i _
  exact congrArg Encodable.encode (signed_floor_quotient _ _ _ (positive s))

end LeanTrominoes.UnaryColumn
end
