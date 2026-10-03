/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteLCompletionRow
import LeanTrominoes.FiniteRectangleCover

/-! # Growing a finite L-tromino box cover on all four sides -/
namespace LeanTrominoes.Tromino.FiniteL
open RectangleCover

/-- Fill the next row; every new tile meets the enlarged rectangle. -/
theorem grow_top {a b : Cell} {tiles : Finset (Finset Cell)}
    (h : Covers Tromino.L a b tiles) :
    ∃ more, tiles⊆more ∧ Covers Tromino.L a (b.1,b.2+1) more := by
  let cells := tiles.biUnion id
  let width := (b.1-a.1+1).toNat
  let added := rowPatches cells a.1 (b.2+1) width
  have width_eq : (width:Int)=b.1-a.1+1 := by dsimp [width]; have ho := h.ordered; omega
  have cell_mem (c : Cell) : c∈cells ↔ ∃ f∈tiles, c∈f := Finset.mem_biUnion
  have fresh : ∀ c∈cells, c.2<(b.2+1)+1 := by
    intro c hc
    obtain ⟨f,hf,hcf⟩ := (cell_mem c).mp hc
    obtain ⟨q,hq,inside⟩ := h.meets f hf
    have near := footprint_near (h.packing.tilesInside f hf).1 hcf hq
    dsimp [Inside] at inside; omega
  have addedPartial := rowPatches_partial cells a.1 (b.2+1) width
  have avoid {f : Finset Cell} (hf : f∈added) {c : Cell} (hc : c∈f) : c∉cells :=
    rowPatches_avoid cells a.1 (b.2+1) width fresh hf hc
  refine ⟨tiles∪added,Finset.subset_union_left,?_,?_,?_,?_⟩
  · have ho := h.ordered; dsimp; omega
  · constructor
    · intro f hf
      rcases Finset.mem_union.mp hf with old|new
      · exact h.packing.tilesInside f old
      · exact addedPartial.tilesInside f new
    · intro f hf g hg c hcf hcg
      rcases Finset.mem_union.mp hf with oldf|newf <;> rcases Finset.mem_union.mp hg with oldg|newg
      · exact h.packing.nonoverlap f oldf g oldg c hcf hcg
      · exact (avoid newg hcg ((cell_mem c).mpr ⟨f,oldf,hcf⟩)).elim
      · exact (avoid newf hcf ((cell_mem c).mpr ⟨g,oldg,hcg⟩)).elim
      · exact addedPartial.nonoverlap f newf g newg c hcf hcg
  · intro f hf
    rcases Finset.mem_union.mp hf with old|new
    · obtain ⟨c,hc,inside⟩ := h.meets f old
      refine ⟨c,hc,?_⟩; dsimp [Inside] at inside ⊢; omega
    · obtain ⟨x,lo,hi,hc⟩ := rowPatches_meet cells a.1 (b.2+1) width new
      refine ⟨(x,b.2+1),hc,?_⟩
      have ho := h.ordered; dsimp [Inside]; omega
  · intro c inside
    by_cases oldrow : c.2≤b.2
    · obtain ⟨f,hf,hc⟩ := h.covers c (by dsimp [Inside] at inside ⊢; omega)
      exact ⟨f,Finset.mem_union_left _ hf,hc⟩
    · have y : c.2=b.2+1 := by dsimp [Inside] at inside; omega
      by_cases oldcell : c∈cells
      · obtain ⟨f,hf,hc⟩ := (cell_mem c).mp oldcell
        exact ⟨f,Finset.mem_union_left _ hf,hc⟩
      · have no : (c.1,b.2+1)∉cells := by simpa only [← y,Prod.mk.eta] using oldcell
        obtain ⟨f,hf,hc⟩ := rowPatches_cover cells a.1 (b.2+1) width c.1
          (by dsimp [Inside] at inside; omega) (by dsimp [Inside] at inside; omega) no
        exact ⟨f,Finset.mem_union_right _ hf,by simpa only [← y,Prod.mk.eta] using hc⟩

/-- Four applications of the row step enlarge each side by one unit. -/
theorem grow_box {a b : Cell} {tiles : Finset (Finset Cell)}
    (h : Covers Tromino.L a b tiles) :
    ∃ more, tiles⊆more ∧ Covers Tromino.L (a.1-1,a.2-1) (b.1+1,b.2+1) more := by
  obtain ⟨t1,s1,h1⟩ := grow_top h
  obtain ⟨t2,s2,h2⟩ := grow_top h1.turn
  obtain ⟨t3,s3,h3⟩ := grow_top h2.turn
  obtain ⟨t4,s4,h4⟩ := grow_top h3.turn
  refine ⟨turn t4,?_,?_⟩
  · have sub := (turn_mono (turn_mono (turn_mono (turn_mono s1)))).trans
      ((turn_mono (turn_mono (turn_mono s2))).trans
        ((turn_mono (turn_mono s3)).trans (turn_mono s4)))
    simpa only [turn_four] using sub
  · convert h4.turn using 1 <;> congr 2 <;> dsimp <;> omega

end LeanTrominoes.Tromino.FiniteL
