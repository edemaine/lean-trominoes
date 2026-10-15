/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteICompletionGeometry
import LeanTrominoes.Tiling.Tromino.Finite.FiniteIntervalFrontier
import Mathlib.Data.Finset.Union

/-! # Four computable frontiers of a finite straight-tromino box cover -/
namespace LeanTrominoes.Tromino.FiniteI
open FiniteInterval

def cellsOf (tiles : Finset (Finset Cell)) : Finset Cell := tiles.biUnion id

theorem mem_cellsOf (tiles : Finset (Finset Cell)) (c : Cell) :
    c∈cellsOf tiles ↔ ∃ f∈tiles, c∈f := by simp [cellsOf]

def row (cells : Finset Cell) (y : Int) : Finset Int :=
  (cells.filter fun c => c.2=y).image Prod.fst

def column (cells : Finset Cell) (x : Int) : Finset Int :=
  (cells.filter fun c => c.1=x).image Prod.snd

@[simp] theorem mem_row (cells : Finset Cell) (x y : Int) :
    x∈row cells y ↔ (x,y)∈cells := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,hc,equal⟩ := Finset.mem_image.mp h
    obtain ⟨hc,hy⟩ := Finset.mem_filter.mp hc
    dsimp at equal hy
    simpa only [equal,hy] using hc
  · intro h
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩

@[simp] theorem mem_column (cells : Finset Cell) (x y : Int) :
    y∈column cells x ↔ (x,y)∈cells := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,hc,equal⟩ := Finset.mem_image.mp h
    obtain ⟨hc,hx⟩ := Finset.mem_filter.mp hc
    dsimp at equal hx
    simpa only [equal,hx] using hc
  · intro h
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_filter.mpr ⟨h,rfl⟩,rfl⟩

structure Boundary (r : Nat) (tiles : Finset (Finset Cell)) : Prop where
  legal : ∀ f∈tiles, Tromino.I.IsFootprint f
  meets : ∀ f∈tiles, ∃ q∈f, q∈Box (-(r:Int),-(r:Int)) (r,r)
  covers : ∀ c∈Box (-(r:Int),-(r:Int)) (r,r), c∈cellsOf tiles

def rightEnd (r : Nat) (tiles : Finset (Finset Cell)) (y : Int) : Int :=
  upper (row (cellsOf tiles) y) r

def leftEnd (r : Nat) (tiles : Finset (Finset Cell)) (y : Int) : Int :=
  lower (row (cellsOf tiles) y) (-(r:Int))

def topEnd (r : Nat) (tiles : Finset (Finset Cell)) (x : Int) : Int :=
  upper (column (cellsOf tiles) x) r

def bottomEnd (r : Nat) (tiles : Finset (Finset Cell)) (x : Int) : Int :=
  lower (column (cellsOf tiles) x) (-(r:Int))

 theorem rightEnd_ge (r : Nat) (tiles : Finset (Finset Cell)) (y : Int) :
    (r:Int)≤rightEnd r tiles y := le_upper _ _
 theorem leftEnd_le (r : Nat) (tiles : Finset (Finset Cell)) (y : Int) :
    leftEnd r tiles y≤-(r:Int) := lower_le _ _
 theorem topEnd_ge (r : Nat) (tiles : Finset (Finset Cell)) (x : Int) :
    (r:Int)≤topEnd r tiles x := le_upper _ _
 theorem bottomEnd_le (r : Nat) (tiles : Finset (Finset Cell)) (x : Int) :
    bottomEnd r tiles x≤-(r:Int) := lower_le _ _

theorem Boundary.right_free {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (k z : Int) (outside : (r:Int)<z) : (z,k)∉cellsOf tiles ↔ rightEnd r tiles k<z := by
  have initial : ∀ y∈row (cellsOf tiles) k, ∀ w, (r:Int)<w → w≤y → w∈row (cellsOf tiles) k := by
    intro y hy w hw hwy
    have covered : (y,k)∈cellsOf tiles := (mem_row _ _ _).mp hy
    obtain ⟨f,hf,hc⟩ := (mem_cellsOf _ _).mp covered
    apply (mem_row _ _ _).mpr
    apply (mem_cellsOf _ _).mpr
    exact ⟨f,hf,right_prefix (h.legal f hf) (h.meets f hf) hc hw hwy⟩
  simpa only [mem_row,rightEnd] using
    free_above (row (cellsOf tiles) k) (r:Int) z initial outside

theorem Boundary.left_free {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (k z : Int) (outside : z<(-(r:Int))) : (z,k)∉cellsOf tiles ↔ z<leftEnd r tiles k := by
  have initial : ∀ y∈row (cellsOf tiles) k, ∀ w, w<(-(r:Int)) → y≤w → w∈row (cellsOf tiles) k := by
    intro y hy w hw hwy
    have covered : (y,k)∈cellsOf tiles := (mem_row _ _ _).mp hy
    obtain ⟨f,hf,hc⟩ := (mem_cellsOf _ _).mp covered
    apply (mem_row _ _ _).mpr
    apply (mem_cellsOf _ _).mpr
    exact ⟨f,hf,left_prefix (h.legal f hf) (h.meets f hf) hc hw hwy⟩
  simpa only [mem_row,leftEnd] using
    free_below (row (cellsOf tiles) k) (-(r:Int)) z initial outside

theorem Boundary.top_free {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (k z : Int) (outside : (r:Int)<z) : (k,z)∉cellsOf tiles ↔ topEnd r tiles k<z := by
  have initial : ∀ y∈column (cellsOf tiles) k, ∀ w, (r:Int)<w → w≤y → w∈column (cellsOf tiles) k := by
    intro y hy w hw hwy
    have covered : (k,y)∈cellsOf tiles := (mem_column _ _ _).mp hy
    obtain ⟨f,hf,hc⟩ := (mem_cellsOf _ _).mp covered
    apply (mem_column _ _ _).mpr
    apply (mem_cellsOf _ _).mpr
    exact ⟨f,hf,top_prefix (h.legal f hf) (h.meets f hf) hc hw hwy⟩
  simpa only [mem_column,topEnd] using
    free_above (column (cellsOf tiles) k) (r:Int) z initial outside

theorem Boundary.bottom_free {r : Nat} {tiles : Finset (Finset Cell)} (h : Boundary r tiles)
    (k z : Int) (outside : z<(-(r:Int))) : (k,z)∉cellsOf tiles ↔ z<bottomEnd r tiles k := by
  have initial : ∀ y∈column (cellsOf tiles) k, ∀ w, w<(-(r:Int)) → y≤w → w∈column (cellsOf tiles) k := by
    intro y hy w hw hwy
    have covered : (k,y)∈cellsOf tiles := (mem_column _ _ _).mp hy
    obtain ⟨f,hf,hc⟩ := (mem_cellsOf _ _).mp covered
    apply (mem_column _ _ _).mpr
    apply (mem_cellsOf _ _).mpr
    exact ⟨f,hf,bottom_prefix (h.legal f hf) (h.meets f hf) hc hw hwy⟩
  simpa only [mem_column,bottomEnd] using
    free_below (column (cellsOf tiles) k) (-(r:Int)) z initial outside

end LeanTrominoes.Tromino.FiniteI
