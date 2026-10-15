/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Completion.FiniteTrominoCompletion
import Mathlib.Tactic

/-! # Straight-tromino geometry at the boundary of a finite box -/
namespace LeanTrominoes.Tromino.FiniteI

def horizontal (x y : Int) : Finset Cell := {(x,y),(x+1,y),(x+2,y)}
def vertical (x y : Int) : Finset Cell := {(x,y),(x,y+1),(x,y+2)}

theorem horizontal_footprint (x y : Int) : Tromino.I.IsFootprint (horizontal x y) := by
  refine ⟨⟨(),.identity,(x,y)⟩,?_⟩
  simp [Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,horizontal]

theorem vertical_footprint (x y : Int) : Tromino.I.IsFootprint (vertical x y) := by
  refine ⟨⟨(),.rotate90,(x,y)⟩,?_⟩
  simp [Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,vertical]

theorem footprint_iff (f : Finset Cell) : Tromino.I.IsFootprint f ↔
    (∃ x y, f=horizontal x y) ∨ (∃ x y, f=vertical x y) := by
  constructor
  · rintro ⟨⟨u,s,⟨x,y⟩⟩,rfl⟩
    cases s
    all_goals simp only [Placement.cells,Tromino.cells,Finset.image_insert,Finset.image_singleton,
      SquareSymmetry.act,Cell.add,neg_zero,neg_add_rev,neg_neg,Int.reduceNeg,add_zero]
    · exact Or.inl ⟨x,y,rfl⟩
    · exact Or.inr ⟨x,y,rfl⟩
    · left; refine ⟨x-2,y,?_⟩; ext c; simp [horizontal]; constructor <;> intro h <;> rcases h with h|h|h <;> simp_all <;> omega
    · right; refine ⟨x,y-2,?_⟩; ext c; simp [vertical]; constructor <;> intro h <;> rcases h with h|h|h <;> simp_all <;> omega
    · exact Or.inl ⟨x,y,rfl⟩
    · exact Or.inr ⟨x,y,rfl⟩
    · left; refine ⟨x-2,y,?_⟩; ext c; simp [horizontal]; constructor <;> intro h <;> rcases h with h|h|h <;> simp_all <;> omega
    · right; refine ⟨x,y-2,?_⟩; ext c; simp [vertical]; constructor <;> intro h <;> rcases h with h|h|h <;> simp_all <;> omega
  · rintro (⟨x,y,rfl⟩|⟨x,y,rfl⟩)
    · exact horizontal_footprint x y
    · exact vertical_footprint x y

@[simp] theorem mem_horizontal (c : Cell) (x y : Int) :
    c∈horizontal x y ↔ c.2=y ∧ x≤c.1 ∧ c.1≤x+2 := by
  rcases c with ⟨a,b⟩
  simp [horizontal,Prod.mk.injEq]
  omega

@[simp] theorem mem_vertical (c : Cell) (x y : Int) :
    c∈vertical x y ↔ c.1=x ∧ y≤c.2 ∧ c.2≤y+2 := by
  rcases c with ⟨a,b⟩
  simp [vertical,Prod.mk.injEq]
  omega

/-- A closed, possibly empty integer rectangle. -/
def Box (a b : Cell) : Set Cell := {c | a.1≤c.1 ∧ c.1≤b.1 ∧ a.2≤c.2 ∧ c.2≤b.2}

/-- A straight tile meeting a box cannot enter an exterior corner quadrant. -/
theorem no_corner {a b c : Cell} {f : Finset Cell} (tile : Tromino.I.IsFootprint f)
    (meets : ∃ q∈f, q∈Box a b) (hc : c∈f) :
    (a.1≤c.1 ∧ c.1≤b.1) ∨ (a.2≤c.2 ∧ c.2≤b.2) := by
  obtain ⟨q,hq,inside⟩ := meets
  rcases (footprint_iff f).mp tile with ⟨x,y,rfl⟩|⟨x,y,rfl⟩
  · have cq := (mem_horizontal c x y).mp hc
    have qq := (mem_horizontal q x y).mp hq
    right; dsimp [Box] at inside; omega
  · have cq := (mem_vertical c x y).mp hc
    have qq := (mem_vertical q x y).mp hq
    left; dsimp [Box] at inside; omega

/-- Outside the top side, any protrusion fills a contiguous initial segment. -/
theorem top_prefix {a b : Cell} {f : Finset Cell} (tile : Tromino.I.IsFootprint f)
    (meets : ∃ q∈f, q∈Box a b) {x y z : Int}
    (covered : (x,y)∈f) (above : b.2<z) (before : z≤y) : (x,z)∈f := by
  obtain ⟨q,hq,inside⟩ := meets
  rcases (footprint_iff f).mp tile with ⟨u,v,rfl⟩|⟨u,v,rfl⟩
  · have cy := (mem_horizontal (x,y) u v).mp covered
    have qq := (mem_horizontal q u v).mp hq
    dsimp [Box] at inside; dsimp at cy; omega
  · have cy := (mem_vertical (x,y) u v).mp covered
    have qq := (mem_vertical q u v).mp hq
    apply (mem_vertical (x,z) u v).mpr
    dsimp [Box] at inside; dsimp at cy ⊢; omega


theorem bottom_prefix {a b : Cell} {f : Finset Cell} (tile : Tromino.I.IsFootprint f)
    (meets : ∃ q∈f, q∈Box a b) {x y z : Int}
    (covered : (x,y)∈f) (outside : z<a.2) (before : y≤z) : (x,z)∈f := by
  obtain ⟨q,hq,inside⟩ := meets
  rcases (footprint_iff f).mp tile with ⟨u,v,rfl⟩|⟨u,v,rfl⟩
  · have cy := (mem_horizontal (x,y) u v).mp covered
    have qq := (mem_horizontal q u v).mp hq
    dsimp [Box] at inside; dsimp at cy; omega
  · have cy := (mem_vertical (x,y) u v).mp covered
    have qq := (mem_vertical q u v).mp hq
    apply (mem_vertical (x,z) u v).mpr
    dsimp [Box] at inside; dsimp at cy ⊢; omega

theorem right_prefix {a b : Cell} {f : Finset Cell} (tile : Tromino.I.IsFootprint f)
    (meets : ∃ q∈f, q∈Box a b) {x y z : Int}
    (covered : (y,x)∈f) (outside : b.1<z) (before : z≤y) : (z,x)∈f := by
  obtain ⟨q,hq,inside⟩ := meets
  rcases (footprint_iff f).mp tile with ⟨u,v,rfl⟩|⟨u,v,rfl⟩
  · have cy := (mem_horizontal (y,x) u v).mp covered
    have qq := (mem_horizontal q u v).mp hq
    apply (mem_horizontal (z,x) u v).mpr
    dsimp [Box] at inside; dsimp at cy ⊢; omega
  · have cy := (mem_vertical (y,x) u v).mp covered
    have qq := (mem_vertical q u v).mp hq
    dsimp [Box] at inside; dsimp at cy; omega

theorem left_prefix {a b : Cell} {f : Finset Cell} (tile : Tromino.I.IsFootprint f)
    (meets : ∃ q∈f, q∈Box a b) {x y z : Int}
    (covered : (y,x)∈f) (outside : z<a.1) (before : y≤z) : (z,x)∈f := by
  obtain ⟨q,hq,inside⟩ := meets
  rcases (footprint_iff f).mp tile with ⟨u,v,rfl⟩|⟨u,v,rfl⟩
  · have cy := (mem_horizontal (y,x) u v).mp covered
    have qq := (mem_horizontal q u v).mp hq
    apply (mem_horizontal (z,x) u v).mpr
    dsimp [Box] at inside; dsimp at cy ⊢; omega
  · have cy := (mem_vertical (y,x) u v).mp covered
    have qq := (mem_vertical q u v).mp hq
    dsimp [Box] at inside; dsimp at cy; omega
end LeanTrominoes.Tromino.FiniteI
