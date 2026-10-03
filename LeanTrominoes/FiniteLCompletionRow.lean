/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteLCompletionGeometry
import Mathlib.Data.Finset.Union

/-! # Filling one row with L-trominoes without disturbing occupied cells -/
namespace LeanTrominoes.Tromino.FiniteL

def pairStart (a : Int) (k : Nat) : Int := a+2*k

def blocked (cells : Finset Cell) (a : Int) (width : Nat) (x y : Int) : Bool :=
  decide ((x,y)∈cells ∨ a+(width:Int)≤x)

@[simp] theorem blocked_false (cells : Finset Cell) (a : Int) (width : Nat) (x y : Int) :
    blocked cells a width x y=false ↔ (x,y)∉cells ∧ x<a+(width:Int) := by
  simp [blocked]

def rowPatches (cells : Finset Cell) (a y : Int) (width : Nat) : Finset (Finset Cell) :=
  (Finset.range ((width+1)/2)).biUnion fun k =>
    patch (blocked cells a width (pairStart a k) y)
      (blocked cells a width (pairStart a k+1) y) (pairStart a k) y

theorem mem_rowPatches (cells : Finset Cell) (a y : Int) (width : Nat) (f : Finset Cell) :
    f∈rowPatches cells a y width ↔ ∃ k, k<(width+1)/2 ∧
      f∈patch (blocked cells a width (pairStart a k) y)
        (blocked cells a width (pairStart a k+1) y) (pairStart a k) y := by
  simp [rowPatches]

theorem rowPatches_partial (cells : Finset Cell) (a y : Int) (width : Nat) :
    Tromino.L.IsPartialTiling Set.univ (rowPatches cells a y width : Set (Finset Cell)) := by
  constructor
  · intro f hf
    obtain ⟨k,_,hp⟩ := (mem_rowPatches _ _ _ _ _).mp hf
    exact ⟨patch_legal _ _ _ _ hp,by simp⟩
  · intro f hf g hg c hcf hcg
    obtain ⟨k,_,hp⟩ := (mem_rowPatches _ _ _ _ _).mp hf
    obtain ⟨l,_,hq⟩ := (mem_rowPatches _ _ _ _ _).mp hg
    have bp := patch_bounds _ _ _ _ hp hcf
    have bq := patch_bounds _ _ _ _ hq hcg
    have equal : k=l := by dsimp [pairStart] at bp bq; omega
    subst l
    exact patch_unique _ _ _ _ hp hq

/-- New tiles avoid all old cells, provided the next row is unused. -/
theorem rowPatches_avoid (cells : Finset Cell) (a y : Int) (width : Nat)
    (fresh : ∀ c∈cells, c.2<y+1) {f : Finset Cell} (hf : f∈rowPatches cells a y width)
    {c : Cell} (hc : c∈f) : c∉cells := by
  obtain ⟨k,_,hp⟩ := (mem_rowPatches _ _ _ _ _).mp hf
  have bound := patch_bounds _ _ _ _ hp hc
  intro old
  have hy := fresh c old
  have bottom : c.2=y := by omega
  rcases patch_bottom _ _ _ _ hp hc bottom with ⟨hx,hfree⟩|⟨hx,hfree⟩
  all_goals
    have no := ((blocked_false _ _ _ _ _).mp hfree).1
    apply no
    have equal : c=(_,y) := Prod.ext hx bottom
    exact equal ▸ old

/-- Every new tile meets the row segment it helps fill. -/
theorem rowPatches_meet (cells : Finset Cell) (a y : Int) (width : Nat)
    {f : Finset Cell} (hf : f∈rowPatches cells a y width) :
    ∃ x, a≤x ∧ x<a+(width:Int) ∧ (x,y)∈f := by
  obtain ⟨k,_,hp⟩ := (mem_rowPatches _ _ _ _ _).mp hf
  rcases patch_meets _ _ _ _ hp with ⟨hc,hfree⟩|⟨hc,hfree⟩
  · exact ⟨pairStart a k,by dsimp [pairStart]; omega,
      ((blocked_false _ _ _ _ _).mp hfree).2,hc⟩
  · exact ⟨pairStart a k+1,by dsimp [pairStart]; omega,
      ((blocked_false _ _ _ _ _).mp hfree).2,hc⟩

/-- All unoccupied cells of the requested row segment are filled. -/
theorem rowPatches_cover (cells : Finset Cell) (a y : Int) (width : Nat) (x : Int)
    (lo : a≤x) (hi : x<a+(width:Int)) (free : (x,y)∉cells) :
    ∃ f∈rowPatches cells a y width, (x,y)∈f := by
  let k := (x-a).toNat/2
  have hk : k<(width+1)/2 := by dsimp [k]; omega
  have position : x=pairStart a k ∨ x=pairStart a k+1 := by dsimp [pairStart,k]; omega
  have empty : blocked cells a width x y=false := (blocked_false _ _ _ _ _).mpr ⟨free,hi⟩
  rcases position with equal|equal
  · have hfree : blocked cells a width (pairStart a k) y=false := equal ▸ empty
    obtain ⟨f,hf,hc⟩ := patch_covers_left (blocked cells a width (pairStart a k+1) y) (pairStart a k) y
    refine ⟨f,(mem_rowPatches _ _ _ _ _).mpr ⟨k,hk,?_⟩,?_⟩
    · simpa only [hfree] using hf
    · simpa only [equal] using hc
  · have hfree : blocked cells a width (pairStart a k+1) y=false := equal ▸ empty
    obtain ⟨f,hf,hc⟩ := patch_covers_right (blocked cells a width (pairStart a k) y) (pairStart a k) y
    refine ⟨f,(mem_rowPatches _ _ _ _ _).mpr ⟨k,hk,?_⟩,?_⟩
    · simpa only [hfree] using hf
    · simpa only [equal] using hc

end LeanTrominoes.Tromino.FiniteL
