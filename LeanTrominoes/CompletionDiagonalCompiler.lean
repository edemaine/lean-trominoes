/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionDiagonalNat
import LeanTrominoes.UnaryColumnCompiler

/-! # Polynomial-time coordinate machines for the diagonal refinement -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.DiagonalRouting
open Computability Turing UnaryColumn
variable {Symbol Index : Type} [Fintype Symbol] [Inhabited Symbol]
  {rows : List Symbol → List Index} {x y : List Symbol → Index → Nat}

private def residueCompiler (cx : Compiler rows x) (cy : Compiler rows y) :
    Compiler rows (fun s i => x s i%2+2*(y s i%4)) := by
  let a := residue cx 2 (by decide) Fin.val
  let b := scale (residue cy 4 (by decide) Fin.val) 2
  exact TM2ComputableInPolyTime.of_eq (add a b) (fun s => by simp [Nat.mul_comm])

def sourceXCompiler (cx : Compiler rows x) (cy : Compiler rows y) :
    Compiler rows (fun s i => natSourceX (x s i) (y s i)) := by
  let bump := residue (residueCompiler cx cy) 8 (by decide)
    (fun r => if r.val/2 = 3 ∨ (r.val/2 = 2 ∧ r.val%2 = 1) then 1 else 0)
  let base := add (halve cx) (divPowTwo cy 2)
  apply TM2ComputableInPolyTime.of_eq (add base bump)
  intro s
  apply List.map_congr_left
  intro i _
  dsimp [base,bump,natSourceX]
  have bound : x s i%2+2*(y s i%4) < 8 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  congr 1
  split_ifs <;> omega

def sourceYCompiler (cx : Compiler rows x) (cy : Compiler rows y) :
    Compiler rows (fun s i => natSourceY (x s i) (y s i)) := by
  let bump := residue (residueCompiler cx cy) 8 (by decide)
    (fun r => if r.val/2 = 3 ∧ r.val%2 = 1 then 1 else 0)
  apply TM2ComputableInPolyTime.of_eq (add (divPowTwo cy 2) bump)
  intro s
  apply List.map_congr_left
  intro i _
  dsimp [bump,natSourceY]
  have bound : x s i%2+2*(y s i%4) < 8 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  congr 1
  split_ifs <;> omega

def roleCompiler (cx : Compiler rows x) (cy : Compiler rows y) :
    Compiler rows (fun s i => (natRole (x s i) (y s i)).val) := by
  let result := residue (residueCompiler cx cy) 8 (by decide)
    (fun r => (natRole (r.val%2) (r.val/2)).val)
  apply TM2ComputableInPolyTime.of_eq result
  intro s
  apply List.map_congr_left
  intro i _
  dsimp
  have bound : x s i%2+2*(y s i%4) < 8 := by omega
  simp only [Nat.mod_eq_of_lt bound]
  have a : (x s i%2+2*(y s i%4))%2 = x s i%2 := by omega
  have b : (x s i%2+2*(y s i%4))/2 = y s i%4 := by omega
  rw [a,b]
  simp [natRole]
end LeanTrominoes.CompletionPattern.DiagonalRouting
