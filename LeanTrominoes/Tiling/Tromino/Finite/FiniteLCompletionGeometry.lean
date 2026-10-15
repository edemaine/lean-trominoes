/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.FiniteTrominoCompletion
import Mathlib.Tactic

/-! # L-trominoes used to extend a covered rectangle by one row -/
namespace LeanTrominoes.Tromino.FiniteL

def twoBottom (x y : Int) : Finset Cell := {(x,y),(x+1,y),(x,y+1)}
def bottomLeft (x y : Int) : Finset Cell := {(x,y),(x,y+1),(x+1,y+1)}
def bottomRight (x y : Int) : Finset Cell := {(x+1,y),(x,y+1),(x+1,y+1)}

theorem twoBottom_legal (x y : Int) : Tromino.L.IsFootprint (twoBottom x y) := by
  refine ⟨⟨(),.identity,(x,y)⟩,?_⟩
  simp [Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,twoBottom]

theorem bottomLeft_legal (x y : Int) : Tromino.L.IsFootprint (bottomLeft x y) := by
  refine ⟨⟨(),.rotate270,(x,y+1)⟩,?_⟩
  ext c
  simp [Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,bottomLeft,or_comm,or_left_comm]

theorem bottomRight_legal (x y : Int) : Tromino.L.IsFootprint (bottomRight x y) := by
  refine ⟨⟨(),.rotate180,(x+1,y+1)⟩,?_⟩
  ext c
  simp [Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,bottomRight,or_comm,or_left_comm,or_assoc]

/-- All cells of an L footprint lie within one unit of every other cell. -/
theorem footprint_near {f : Finset Cell} (tile : Tromino.L.IsFootprint f)
    {c q : Cell} (hc : c∈f) (hq : q∈f) :
    q.1-1≤c.1 ∧ c.1≤q.1+1 ∧ q.2-1≤c.2 ∧ c.2≤q.2+1 := by
  obtain ⟨⟨u,s,⟨x,y⟩⟩,rfl⟩ := tile
  cases s
  all_goals simp only [Placement.cells,Tromino.cells,Finset.image_insert,Finset.image_singleton,
    SquareSymmetry.act,Cell.add,Finset.mem_insert,Finset.mem_singleton] at hc hq
  all_goals rcases hc with rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl <;> dsimp <;> omega

/-- The two bits say which bottom-row cells are already occupied. -/
def patch (left right : Bool) (x y : Int) : Finset (Finset Cell) :=
  match left,right with
  | false,false => {twoBottom x y}
  | false,true => {bottomLeft x y}
  | true,false => {bottomRight x y}
  | true,true => ∅

theorem patch_legal (left right : Bool) (x y : Int) {f : Finset Cell}
    (hf : f∈patch left right x y) : Tromino.L.IsFootprint f := by
  cases left <;> cases right <;> simp [patch] at hf
  · subst f; exact twoBottom_legal x y
  · subst f; exact bottomLeft_legal x y
  · subst f; exact bottomRight_legal x y

theorem patch_unique (left right : Bool) (x y : Int) {f g : Finset Cell}
    (hf : f∈patch left right x y) (hg : g∈patch left right x y) : f=g := by
  cases left <;> cases right <;> simp_all [patch]

theorem patch_bounds (left right : Bool) (x y : Int) {f : Finset Cell} {c : Cell}
    (hf : f∈patch left right x y) (hc : c∈f) :
    x≤c.1 ∧ c.1≤x+1 ∧ y≤c.2 ∧ c.2≤y+1 := by
  cases left <;> cases right <;> simp [patch] at hf
  all_goals subst f; simp only [twoBottom,bottomLeft,bottomRight,Finset.mem_insert,Finset.mem_singleton] at hc
  all_goals rcases hc with rfl|rfl|rfl <;> dsimp <;> omega

theorem patch_bottom (left right : Bool) (x y : Int) {f : Finset Cell} {c : Cell}
    (hf : f∈patch left right x y) (hc : c∈f) (bottom : c.2=y) :
    (c.1=x ∧ left=false) ∨ (c.1=x+1 ∧ right=false) := by
  cases left <;> cases right <;> simp [patch] at hf
  all_goals subst f; simp only [twoBottom,bottomLeft,bottomRight,Finset.mem_insert,Finset.mem_singleton] at hc
  all_goals rcases hc with rfl|rfl|rfl <;> dsimp at bottom ⊢ <;> first | omega | simp

theorem patch_meets (left right : Bool) (x y : Int) {f : Finset Cell}
    (hf : f∈patch left right x y) :
    ((x,y)∈f ∧ left=false) ∨ ((x+1,y)∈f ∧ right=false) := by
  cases left <;> cases right <;> simp [patch] at hf
  all_goals subst f; simp [twoBottom,bottomLeft,bottomRight]

theorem patch_covers_left (right : Bool) (x y : Int) :
    ∃ f∈patch false right x y, (x,y)∈f := by
  cases right <;> simp [patch,twoBottom,bottomLeft]

theorem patch_covers_right (left : Bool) (x y : Int) :
    ∃ f∈patch left false x y, (x+1,y)∈f := by
  cases left <;> simp [patch,twoBottom,bottomRight]

end LeanTrominoes.Tromino.FiniteL
