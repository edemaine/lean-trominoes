/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetAssembly

/-! # Unique placement records for straight tromino footprints -/
namespace LeanTrominoes.Gadget.CanonicalI

def vertical : SquareSymmetry → Bool
  | .rotate90 | .rotate270 | .reflectDiagonal | .reflectAntidiagonal => true
  | _ => false

def correction : SquareSymmetry → Cell
  | .rotate180 | .reflectY => (-2,0)
  | .rotate270 | .reflectAntidiagonal => (0,-2)
  | _ => (0,0)

def normalize (p : Placement Unit) : Placement Unit :=
  ⟨(),if vertical p.symmetry then .rotate90 else .identity,Cell.add p.offset (correction p.symmetry)⟩

def Canonical (p : Placement Unit) : Prop := p.symmetry = .identity ∨ p.symmetry = .rotate90

theorem normalize_canonical (p : Placement Unit) : Canonical (normalize p) := by
  unfold Canonical normalize
  split <;> simp

theorem normalize_cells (p : Placement Unit) :
    (normalize p).cells (fun _ => Tromino.I.cells) = p.cells (fun _ => Tromino.I.cells) := by
  cases p with
  | mk kind symmetry offset =>
    cases kind
    rcases offset with ⟨x,y⟩
    cases symmetry <;>
      ext cell <;>
      rcases cell with ⟨cx,cy⟩ <;>
      simp [normalize,vertical,correction,Placement.cells,Tromino.cells,SquareSymmetry.act,Cell.add,Prod.mk.injEq] <;>
      omega

theorem canonical_cells_injective {p q : Placement Unit} (hp : Canonical p) (hq : Canonical q)
    (same : p.cells (fun _ => Tromino.I.cells) = q.cells (fun _ => Tromino.I.cells)) : p = q := by
  rcases p with ⟨⟨⟩,ps,⟨px,py⟩⟩
  rcases q with ⟨⟨⟩,qs,⟨qx,qy⟩⟩
  have pOrigin := Tromino.offset_mem_placement_cells .I (Placement.mk () ps (px,py))
  have qOrigin := Tromino.offset_mem_placement_cells .I (Placement.mk () qs (qx,qy))
  rw [same] at pOrigin
  rw [← same] at qOrigin
  have pEnd : Cell.add (px,py) (ps.act (2,0)) ∈ (Placement.mk () qs (qx,qy)).cells (fun _ => Tromino.I.cells) := by
    rw [← same,Placement.mem_cells_iff]
    exact ⟨(2,0),by simp [Tromino.cells],rfl⟩
  change ps = .identity ∨ ps = .rotate90 at hp
  change qs = .identity ∨ qs = .rotate90 at hq
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp only [Placement.cells,Tromino.cells,Finset.image_insert,Finset.image_singleton,
      hp,hq,SquareSymmetry.act,Cell.add,Int.add_zero,
      Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at pOrigin qOrigin pEnd
  all_goals simp only [Placement.mk.injEq,hp,hq,true_and,and_false,false_and,reduceCtorEq,Prod.mk.injEq]
  all_goals omega

theorem normalize_translate (offset : Cell) (p : Placement Unit) :
    normalize (translatePlacement offset p) = translatePlacement offset (normalize p) := by
  apply Placement.ext
  · rfl
  · rfl
  · ext <;> simp [normalize,translatePlacement,Cell.add,add_assoc]

theorem translate_canonical (offset : Cell) {p : Placement Unit} (hp : Canonical p) :
    Canonical (translatePlacement offset p) := hp

end LeanTrominoes.Gadget.CanonicalI
