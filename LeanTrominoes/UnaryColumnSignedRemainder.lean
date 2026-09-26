/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnaryColumnDivisionCompiler
import LeanTrominoes.UnaryColumnModuloCompiler

/-! # Native nonnegative remainders of signed coordinate columns -/
noncomputable section
namespace LeanTrominoes.UnaryColumn
open Turing

theorem signed_remainder (p n d : Nat) (hd : 0 < d) :
    (p%d+d-n%d)%d = (((p:Int)-n)%(d:Int)).toNat := by
  have hn := Nat.mod_lt n hd
  have hc : (((p%d+d-n%d):Nat):Int) = ((p%d:Nat):Int)+d-(n%d:Nat) := by omega
  have eq : (((p%d+d-n%d)%d:Nat):Int) = ((p:Int)-n)%(d:Int) := by
    rw [Int.natCast_emod,hc]
    simp only [Int.sub_emod,Int.add_emod,Int.natCast_emod,Int.emod_self,
      Int.emod_emod,add_zero]
  exact congrArg Int.toNat eq

variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {p n : List Symbol → Index → Nat}
  {divisor : List Symbol → Nat}

def modulo (cp : Compiler rows p) (cd : ScalarCompiler divisor) (positive : ∀ s, 0 < divisor s) :
    Compiler rows (fun s i => p s i % divisor s) :=
  boundedMod cp cd (columnBound cp) positive (fun s i hi => by
    have := List.le_sum_of_mem (List.mem_map.mpr ⟨i,hi,rfl⟩ : p s i ∈ (rows s).map (p s))
    omega)

def signedRemainder (cp : Compiler rows p) (cn : Compiler rows n)
    (cd : ScalarCompiler divisor) (positive : ∀ s, 0 < divisor s) :
    Compiler rows (fun s i => (((p s i:Int)-n s i)%(divisor s:Int)).toNat) := by
  let physical := modulo (sub (add (modulo cp cd positive) (broadcast cp cd)) (modulo cn cd positive)) cd positive
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  apply List.map_congr_left
  intro i _
  exact signed_remainder _ _ _ (positive s)

end LeanTrominoes.UnaryColumn
end
