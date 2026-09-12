/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeExtrusion
import LeanTrominoes.PolyominoConnectivity

/-! # Face connectivity and a finite spanning-tree certificate -/

namespace LeanTrominoes

def Voxel.FaceAdjacent (a b : Voxel) : Prop :=
  (a.2 = b.2 ∧ Cell.SideAdjacent a.1 b.1) ∨
    (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2))

instance : DecidableRel Voxel.FaceAdjacent := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

def Polycube.faceGraph (shape : Polycube) : SimpleGraph {c // c ∈ shape} where
  Adj a b := Voxel.FaceAdjacent a.val b.val
  symm := ⟨by
    intro a b h
    simp only [Voxel.FaceAdjacent, Cell.SideAdjacent, Prod.ext_iff] at h ⊢
    omega⟩
  loopless := ⟨by
    intro a h
    simp only [Voxel.FaceAdjacent, Cell.SideAdjacent] at h
    omega⟩

def Polycube.IsConnected (shape : Polycube) : Prop := shape.faceGraph.Connected

namespace Polycube

/-- A strictly decreasing spanning tree certifies face connectivity. -/
theorem connected_of_predecessor (shape : Polycube) (root : Voxel)
    (hroot : root ∈ shape) (previous : Voxel → Voxel) (rank : Voxel → Nat)
    (certificate : ∀ c ∈ shape, c ≠ root →
      previous c ∈ shape ∧ Voxel.FaceAdjacent c (previous c) ∧
        rank (previous c) < rank c) : IsConnected shape := by
  let r : {c // c ∈ shape} := ⟨root, hroot⟩
  have reach (c : {c // c ∈ shape}) : shape.faceGraph.Reachable c r := by
    generalize hr : rank c.val = n
    induction n using Nat.strong_induction_on generalizing c with
    | h n ih =>
      by_cases hc : c.val = root
      · have he : c = r := Subtype.ext hc
        rw [he]
      · obtain ⟨hp, ha, lt⟩ := certificate c.val c.property hc
        let p : {c // c ∈ shape} := ⟨previous c.val, hp⟩
        have edge : shape.faceGraph.Adj c p := ha
        exact edge.reachable.trans (ih _ (hr ▸ lt) p rfl)
  letI : Nonempty {c // c ∈ shape} := ⟨r⟩
  exact ⟨fun a b => (reach a).trans (reach b).symm⟩

/-- Embed the adjacency graph of a planar shape in a layer of a polycube. -/
def layerHom (shape : Polyomino) (target : Polycube) (z : Int)
    (inside : ∀ c ∈ shape, (c, z) ∈ target) : shape.sideGraph →g target.faceGraph where
  toFun c := ⟨(c.val, z), inside c.val c.property⟩
  map_rel' h := Or.inl ⟨rfl, h⟩

/-- A connected cap joins every component that has a path to the cap's footprint.
The bottom layer itself need not be connected, nor contained in the cap.
-/
theorem capped_one_connected (shape cap : Polyomino)
    (hc : Polyomino.IsConnected cap)
    (attach : ∀ q : {c // c ∈ shape},
      ∃ r : {c // c ∈ shape}, r.val ∈ cap ∧ shape.sideGraph.Reachable q r) :
    IsConnected (capped shape cap {0} 1) := by
  let target := capped shape cap {0} 1
  let bottom := layerHom shape target 0 (by intro c h; simp [target, h])
  let top := layerHom cap target 1 (by intro c h; simp [target, h])
  obtain ⟨root⟩ := hc.nonempty
  have reach (c : {c // c ∈ target}) : target.faceGraph.Reachable c (top root) := by
    have hc' := (mem_capped shape cap {0} 1 c.val).mp c.property
    rcases hc' with ⟨hs, hz⟩ | ⟨hs, hz⟩
    · have hz' : c.val.2 = 0 := Finset.mem_singleton.mp hz
      let q : {c // c ∈ shape} := ⟨c.val.1, hs⟩
      obtain ⟨r, hr, path⟩ := attach q
      let rtop : {c // c ∈ cap} := ⟨r.val, hr⟩
      have start : c = bottom q := Subtype.ext (Prod.ext rfl hz')
      have edge : target.faceGraph.Adj (bottom r) (top rtop) :=
        Or.inr ⟨rfl, Or.inl rfl⟩
      rw [start]
      exact (path.map bottom).trans (edge.reachable.trans ((hc.preconnected rtop root).map top))
    · let q : {c // c ∈ cap} := ⟨c.val.1, hs⟩
      have start : c = top q := Subtype.ext (Prod.ext rfl hz)
      rw [start]
      exact (hc.preconnected q root).map top
  letI : Nonempty {c // c ∈ target} := ⟨top root⟩
  exact ⟨fun a b => (reach a).trans (reach b).symm⟩

end Polycube
end LeanTrominoes
