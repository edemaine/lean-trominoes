/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.LocalWindowPeriodicModel

/-! # Pumping a finite-alphabet configuration on a skew cylinder -/
namespace LeanTrominoes.Cylinder
open Gadget.PeriodicOrthogonalDrawing
set_option maxHeartbeats 1500000

variable {α : Type}
def IsPeriod (f : Cell → α) (v : Cell) : Prop := ∀ c, f (Cell.add c v) = f c

theorem period_multiples {f : Cell → α} {v : Cell} (h : IsPeriod f v) (i : Int) :
    ∀ c, f (Cell.add c (Cell.scale i v)) = f c := by
  induction i using Int.induction_on with
  | zero => intro c; simpa [Cell.add,Cell.scale]
  | succ n ih =>
    intro c
    rw [show Cell.add c (Cell.scale ((n:Int)+1) v) = Cell.add (Cell.add c (Cell.scale n v)) v by
      ext <;> dsimp [Cell.add,Cell.scale] <;> ring,h,ih]
  | pred n ih =>
    intro c
    have hh := h (Cell.add c (Cell.scale (-(n:Int)-1) v))
    rw [show Cell.add (Cell.add c (Cell.scale (-(n:Int)-1) v)) v = Cell.add c (Cell.scale (-(n:Int)) v) by
      ext <;> dsimp [Cell.add,Cell.scale] <;> ring] at hh
    exact hh.symm.trans (ih c)

def column (a : Nat) (c : Cell) : Fin (a+1) := residue c.1 a
def row (a : Nat) (b : Int) (c : Cell) : Int := c.2 - (c.1 / (a+1:Int))*b

theorem column_vertical (a : Nat) (c : Cell) (z : Int) : column a (Cell.add c (0,z)) = column a c := by
  simp [column,Cell.add]
theorem row_vertical (a : Nat) (b : Int) (c : Cell) (z : Int) :
    row a b (Cell.add c (0,z)) = row a b c+z := by dsimp [row,Cell.add]; ring

theorem column_period (a : Nat) (b : Int) (c : Cell) :
    column a (Cell.add c (a+1,b)) = column a c := by
  apply Fin.ext; simp [column,residue,Cell.add,Int.add_emod]
theorem row_period (a : Nat) (b : Int) (c : Cell) :
    row a b (Cell.add c (a+1,b)) = row a b c := by
  simp only [row,Cell.add]
  have eq := Int.add_mul_ediv_right c.1 1 (show (a+1:Int) ≠ 0 by omega)
  simp only [one_mul] at eq
  rw [eq]
  ring

def delta (a : Nat) (b : Int) (i : Fin (a+1)) (d : Cell) : Int :=
  d.2-((i.val+d.1)/(a+1:Int))*b

theorem row_add (a : Nat) (b : Int) (c d : Cell) :
    row a b (Cell.add c d) = row a b c + delta a b (column a c) d := by
  have split : c.1+d.1 = (c.1%(a+1:Int)+d.1)+(c.1/(a+1:Int))*(a+1:Int) := by
    have h := Int.emod_add_ediv_mul c.1 (a+1:Int); omega
  simp only [row,delta,column,residue_val_int,Cell.add]
  rw [split,Int.add_mul_ediv_right _ _ (by omega)]
  ring

theorem normalize {f : Cell → α} (a : Nat) (b : Int)
    (periodic : IsPeriod f (a+1,b)) (c : Cell) :
    f c = f ((column a c).val,row a b c) := by
  have h := period_multiples periodic (c.1/(a+1:Int)) (((column a c).val:Int),row a b c)
  have eq : Cell.add (((column a c).val:Int),row a b c)
      (Cell.scale (c.1/(a+1:Int)) (a+1,b)) = c := by
    ext
    · simp only [column,residue_val_int,Cell.add,Cell.scale]
      exact Int.emod_add_ediv_mul _ _
    · simp [row,Cell.add,Cell.scale]
  rw [eq] at h; exact h

/-- A configuration with a skew period has a doubly periodic local model.
Each copied neighborhood is displaced vertically by a multiple of `n+1`. -/
theorem skew_model [Fintype α] (f : Cell → α) (a : Nat) (b : Int)
    (periodic : IsPeriod f (a+1,b)) (D : Finset Cell) (n : Nat) :
    ∃ p : Nat, 0 < p ∧ ∃ g : Cell → α,
      IsPeriod g (a+1,b) ∧ IsPeriod g (0,p) ∧
      ∀ c, ∃ k : Int, ∀ d ∈ D,
        g (Cell.add c d) = f (Cell.add (Cell.add c d) (0,(n+1:Int)*k)) := by
  classical
  let R := (Finset.univ.product D).sum fun z => (delta a b z.1 z.2).natAbs
  have bound (i : Fin (a+1)) (d : Cell) (hd : d ∈ D) :
      -(R:Int) ≤ delta a b i d ∧ delta a b i d ≤ R := by
    have le : (delta a b i d).natAbs ≤ R :=
      Finset.single_le_sum (a := (i,d)) (s := Finset.univ.product D)
        (f := fun z : Fin (a+1) × Cell => (delta a b z.1 z.2).natAbs)
        (fun z _ => Nat.zero_le _) (Finset.mem_product.mpr ⟨Finset.mem_univ i,hd⟩)
    have ha := Int.natCast_natAbs (delta a b i d)
    exact ⟨by omega,by omega⟩
  let q : Int → Fin (a+1) → α := fun y i => f (i.val,y)
  obtain ⟨p,hp,s,sp,copy⟩ := LocalWindow.periodic_local_copy q R n
  let g : Cell → α := fun c => s (row a b c) (column a c)
  refine ⟨p,hp,g,?_,?_,?_⟩
  · intro c; simp only [g,column_period,row_period]
  · intro c; simp only [g,column_vertical,row_vertical,sp]
  · intro c
    obtain ⟨y,⟨k,hk⟩,copied⟩ := copy (row a b c)
    refine ⟨k,?_⟩
    intro d hd
    have h := congrFun (copied (delta a b (column a c) d) (bound _ d hd).1 (bound _ d hd).2) (column a (Cell.add c d))
    dsimp [g]
    rw [row_add]
    rw [h,normalize a b periodic (Cell.add (Cell.add c d) (0,(n+1:Int)*k))]
    rw [column_vertical,row_vertical,row_add]
    dsimp only [q]
    push_cast at hk
    congr 2 <;> omega
end LeanTrominoes.Cylinder
