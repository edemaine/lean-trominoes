/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationPolycubes

/-! # Horizontal extrusions need only two fixed translation-only tiles -/

namespace LeanTrominoes.ThreeTranslationPolycubes

theorem extruded_cells {ι : Type*} (shapes : ι → Polyomino) (layers : Finset Int)
    (kind : ι) (s : SquareSymmetry) (offset : Voxel) (c : Voxel) :
    c ∈ (VoxelPlacement.mk kind ⟨s,false,0⟩ offset).cells (fun k => Polycube.extrude (shapes k) layers) ↔
      c.1 ∈ (Placement.mk kind s offset.1).cells shapes ∧ c.2-offset.2 ∈ layers := by
  simp only [VoxelPlacement.mem_cells_iff,Placement.mem_cells_iff,Polycube.mem_extrude]
  constructor
  · rintro ⟨⟨q,z⟩,⟨hq,hz⟩,eq⟩
    have xy : Cell.add offset.1 (s.act q) = c.1 := congrArg Prod.fst eq
    have zz : offset.2+z = c.2 := congrArg Prod.snd eq
    have zeq : c.2-offset.2 = z := by omega
    exact ⟨⟨q,hq,xy⟩,zeq.symm ▸ hz⟩
  · rintro ⟨⟨q,hq,eq⟩,hz⟩
    refine ⟨(q,c.2-offset.2),⟨hq,hz⟩,?_⟩
    change (Cell.add offset.1 (s.act q),offset.2+(c.2-offset.2)) = c
    exact Prod.ext eq (by omega)

def normalize (p : VoxelPlacement Bool) : VoxelPlacement (Option Bool) :=
  if p.kind then ⟨none,CubeSymmetry.identity,p.offset⟩
  else ⟨some (ThreeTranslationPolyominoes.vertical p.symmetry.planar),CubeSymmetry.identity,
    (Cell.add p.offset.1 (ThreeTranslationPolyominoes.correction p.symmetry.planar),p.offset.2)⟩

theorem normalize_cells (layers : Finset Int) (q : Polycube) (p : VoxelPlacement Bool) (legal : Allowed p) :
    (normalize p).cells (tiles layers q) = p.cells (Polycube.pairTiles (Polycube.extrude PlusRefinement.bumpy layers) q) := by
  rcases p with ⟨kind,⟨s,flip,axis⟩,offset⟩
  obtain ⟨ha,hf,hs⟩ := legal
  change axis = 0 at ha
  change flip = false at hf
  subst axis
  subst flip
  cases kind with
  | true =>
    have eq : s = .identity := hs rfl
    subst s
    rfl
  | false =>
    have planar := ThreeTranslationPolyominoes.normalize_cells ∅ (Placement.mk false s offset.1) (by simp [ThreeTranslationPolyominoes.Allowed])
    ext c
    change c ∈ (VoxelPlacement.mk () ⟨.identity,false,0⟩
      (Cell.add offset.1 (ThreeTranslationPolyominoes.correction s),offset.2)).cells
      (fun _ => Polycube.extrude (ThreeTranslationPolyominoes.fixed (ThreeTranslationPolyominoes.vertical s)) layers) ↔
      c ∈ (VoxelPlacement.mk () ⟨s,false,0⟩ offset).cells (fun _ => Polycube.extrude PlusRefinement.bumpy layers)
    rw [extruded_cells,extruded_cells]
    apply and_congr_left
    intro _
    exact Iff.of_eq (congrArg (fun shape : Finset Cell => c.1 ∈ shape) planar)

theorem normalize_legal (p : VoxelPlacement Bool) : (normalize p).symmetry = CubeSymmetry.identity := by
  unfold normalize
  split <;> rfl

def forget (p : VoxelPlacement (Option Bool)) : VoxelPlacement Bool :=
  match p.kind with
  | none => ⟨true,CubeSymmetry.identity,p.offset⟩
  | some v => ⟨false,⟨if v then .rotate90 else .identity,false,0⟩,p.offset⟩

theorem forget_cells (layers : Finset Int) (q : Polycube) (p : VoxelPlacement (Option Bool))
    (legal : p.symmetry = CubeSymmetry.identity) :
    (forget p).cells (Polycube.pairTiles (Polycube.extrude PlusRefinement.bumpy layers) q) = p.cells (tiles layers q) := by
  rcases p with ⟨kind,s,offset⟩
  change s = CubeSymmetry.identity at legal
  subst s
  cases kind with
  | none => rfl
  | some v =>
    ext c
    change c ∈ (VoxelPlacement.mk () ⟨if v then .rotate90 else .identity,false,0⟩ offset).cells
      (fun _ => Polycube.extrude PlusRefinement.bumpy layers) ↔
      c ∈ (VoxelPlacement.mk () ⟨.identity,false,0⟩ offset).cells
      (fun _ => Polycube.extrude (ThreeTranslationPolyominoes.fixed v) layers)
    rw [extruded_cells,extruded_cells]
    cases v <;> simp [ThreeTranslationPolyominoes.fixed,Placement.cells,SquareSymmetry.act,
      Finset.image_image,Function.comp_def]

theorem forget_legal (p : VoxelPlacement (Option Bool)) : Allowed (forget p) := by
  rcases p with ⟨kind,s,offset⟩
  cases kind <;> simp [Allowed,forget,CubeSymmetry.identity]

theorem translationTileable_iff (layers : Finset Int) (q : Polycube) (region : Set Voxel) :
    VoxelTranslationTileable (tiles layers q) region ↔
      VoxelTileableWith (Polycube.pairTiles (Polycube.extrude PlusRefinement.bumpy layers) q) region Allowed := by
  constructor
  · intro h
    exact h.map_cells forget (forget_cells layers q) (fun p _ => forget_legal p)
  · intro h
    exact h.map_cells normalize (normalize_cells layers q) (fun p _ => normalize_legal p)

end LeanTrominoes.ThreeTranslationPolycubes
