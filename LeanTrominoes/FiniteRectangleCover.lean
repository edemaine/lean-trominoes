/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoCompletion
import LeanTrominoes.TilingSymmetry
import Mathlib.Tactic

/-! # Finite partial tilings covering a rectangle, and their rotations -/
namespace LeanTrominoes.Tromino
namespace RectangleCover

def Inside (a b c : Cell) : Prop := a.1≤c.1 ∧ c.1≤b.1 ∧ a.2≤c.2 ∧ c.2≤b.2

structure Covers (t : Tromino) (a b : Cell) (tiles : Finset (Finset Cell)) : Prop where
  ordered : a.1≤b.1 ∧ a.2≤b.2
  packing : t.IsPartialTiling Set.univ (tiles : Set (Finset Cell))
  meets : ∀ f∈tiles, ∃ c∈f, Inside a b c
  covers : ∀ c, Inside a b c → ∃ f∈tiles, c∈f

def orientFootprint (s : SquareSymmetry) (f : Finset Cell) : Finset Cell := f.image s.act

def orientTiles (s : SquareSymmetry) (tiles : Finset (Finset Cell)) : Finset (Finset Cell) :=
  tiles.image (orientFootprint s)

theorem orientFootprint_legal {t : Tromino} {f : Finset Cell}
    (h : t.IsFootprint f) (s : SquareSymmetry) : t.IsFootprint (orientFootprint s f) := by
  obtain ⟨p,rfl⟩ := h
  refine ⟨p.orient s,?_⟩
  simp only [Placement.cells,Placement.orient,orientFootprint,Finset.image_image,Function.comp_def,
    SquareSymmetry.act_add,SquareSymmetry.act_compose]

theorem mem_orientFootprint (s : SquareSymmetry) (f : Finset Cell) (c : Cell) :
    s.act c∈orientFootprint s f ↔ c∈f := by
  exact Finset.mem_image.trans (by
    constructor
    · rintro ⟨q,hq,equal⟩; exact s.act_injective equal ▸ hq
    · intro hc; exact ⟨c,hc,rfl⟩)

theorem orientTiles_mono (s : SquareSymmetry) {tiles more : Finset (Finset Cell)}
    (sub : tiles⊆more) : orientTiles s tiles⊆orientTiles s more := Finset.image_subset_image sub

theorem orient_partial {t : Tromino} {tiles : Finset (Finset Cell)}
    (h : t.IsPartialTiling Set.univ (tiles : Set (Finset Cell))) (s : SquareSymmetry) :
    t.IsPartialTiling Set.univ (orientTiles s tiles : Set (Finset Cell)) := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    exact ⟨orientFootprint_legal (h.tilesInside g hg).1 s,by simp⟩
  · intro f hf g hg c hcf hcg
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp hcf
    obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp hcg
    have same := s.act_injective (ex.trans ey.symm)
    have equal := h.nonoverlap a ha b hb x hx (same.symm ▸ hy)
    exact congrArg (orientFootprint s) equal

def turn (tiles : Finset (Finset Cell)) := orientTiles .rotate90 tiles

theorem turn_mono {tiles more : Finset (Finset Cell)} (sub : tiles⊆more) : turn tiles⊆turn more :=
  orientTiles_mono _ sub

theorem turn_four (tiles : Finset (Finset Cell)) : turn (turn (turn (turn tiles)))=tiles := by
  simp [turn,orientTiles,orientFootprint,Finset.image_image,Function.comp_def,SquareSymmetry.act]

theorem Covers.turn {t : Tromino} {a b : Cell} {tiles : Finset (Finset Cell)}
    (h : Covers t a b tiles) : Covers t (-b.2,a.1) (-a.2,b.1) (turn tiles) := by
  constructor
  · dsimp; have ho := h.ordered; omega
  · exact orient_partial h.packing .rotate90
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨c,hc,inside⟩ := h.meets g hg
    refine ⟨SquareSymmetry.rotate90.act c,(mem_orientFootprint _ _ _).mpr hc,?_⟩
    dsimp [Inside,SquareSymmetry.act] at inside ⊢; omega
  · intro c inside
    let q : Cell := (c.2,-c.1)
    have iq : Inside a b q := by dsimp [Inside,q] at inside ⊢; omega
    obtain ⟨f,hf,hq⟩ := h.covers q iq
    refine ⟨orientFootprint .rotate90 f,Finset.mem_image.mpr ⟨f,hf,rfl⟩,?_⟩
    have hc := (mem_orientFootprint .rotate90 f q).mpr hq
    simpa only [q,SquareSymmetry.act,neg_neg,Prod.mk.eta] using hc

end RectangleCover
end LeanTrominoes.Tromino
