/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteTrominoWitness
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # A computable bounding box for any finite preplacement -/
namespace LeanTrominoes.Tromino.FiniteWitness

def interval (r : Nat) : Finset Int :=
  (Finset.range (2*r+1)).image fun k : Nat => (k:Int)-r

@[simp] theorem mem_interval (r : Nat) (x : Int) :
    x∈interval r ↔ -(r:Int)≤x ∧ x≤r := by
  simp only [interval,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨k,hk,equal⟩; omega
  · intro h; exact ⟨(x+r).toNat,by omega,by omega⟩

def box (r : Nat) : Finset Cell := (interval r).product (interval r)

@[simp] theorem mem_box (r : Nat) (c : Cell) :
    c∈box r ↔ -(r:Int)≤c.1 ∧ c.1≤r ∧ -(r:Int)≤c.2 ∧ c.2≤r := by
  simp [box,and_assoc]

def radius (prefill : Finset (Finset Cell)) : Nat :=
  (prefill.biUnion id).sup fun c => max c.1.natAbs c.2.natAbs

theorem inside_box (prefill : Finset (Finset Cell)) (f : Finset Cell) (hf : f∈prefill)
    (c : Cell) (hc : c∈f) : c∈box (radius prefill) := by
  have member : c∈prefill.biUnion id := Finset.mem_biUnion.mpr ⟨f,hf,hc⟩
  have bound : max c.1.natAbs c.2.natAbs ≤ radius prefill := by
    exact Finset.le_sup (f := fun c : Cell => max c.1.natAbs c.2.natAbs) member
  have xbound : c.1.natAbs≤radius prefill := (Nat.le_max_left _ _).trans bound
  have ybound : c.2.natAbs≤radius prefill := (Nat.le_max_right _ _).trans bound
  have xx := Int.natCast_natAbs c.1
  have yy := Int.natCast_natAbs c.2
  apply (mem_box _ _).mpr
  have hx : |c.1|≤(radius prefill:Int) := by omega
  have hy : |c.2|≤(radius prefill:Int) := by omega
  exact ⟨(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hy).1,(abs_le.mp hy).2⟩

theorem completion_meets_box (t : Tromino) (prefill : Finset (Finset Cell))
    (completion : t.Completable Set.univ (prefill : Set (Finset Cell))) :
    ∀ f∈prefill, ∃ c∈box (radius prefill), c∈f := by
  obtain ⟨all,h,retained⟩ := completion
  intro f hf
  obtain ⟨p,equal⟩ := (h.tilesInside f (retained hf)).1
  have hc : p.offset∈f := equal ▸ t.offset_mem_placement_cells p
  exact ⟨p.offset,inside_box prefill f hf p.offset hc,hc⟩

end LeanTrominoes.Tromino.FiniteWitness
