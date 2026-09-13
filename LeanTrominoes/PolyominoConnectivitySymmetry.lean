/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoConnectivity

/-! # Grid symmetries preserve polyomino connectivity -/

namespace LeanTrominoes

theorem Cell.SideAdjacent.symmetry {a b : Cell} (h : Cell.SideAdjacent a b) (s : SquareSymmetry) :
    Cell.SideAdjacent (s.act a) (s.act b) := by
  cases s <;> simp only [Cell.SideAdjacent,SquareSymmetry.act] at * <;> omega

theorem Polyomino.IsConnected.symmetry {shape : Polyomino} (h : Polyomino.IsConnected shape)
    (s : SquareSymmetry) : Polyomino.IsConnected (shape.image s.act) := by
  let f : shape.sideGraph →g Polyomino.sideGraph (shape.image s.act) :=
    { toFun := fun c => ⟨s.act c.val,Finset.mem_image.mpr ⟨c.val,c.property,rfl⟩⟩
      map_rel' := fun edge => Cell.SideAdjacent.symmetry edge s }
  have surjective : Function.Surjective f := by
    intro c
    obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp c.property
    exact ⟨⟨p,hp⟩,Subtype.ext eq⟩
  exact SimpleGraph.Connected.map f surjective h

end LeanTrominoes
