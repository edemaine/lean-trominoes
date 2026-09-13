/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolycubeFiniteSearch
import LeanTrominoes.PlaneTilingSearchComputability

/-! # Primitive-recursive finite search for two-tile plane tilings -/

namespace LeanTrominoes.VoxelTilingSearch

attribute [local instance] Classical.propDecidable

open Computability

def symmetryEquiv : CubeSymmetry ≃ SquareSymmetry × Bool × Fin 3 where
  toFun s := (s.planar, s.flip, s.axis)
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by rcases s with ⟨p, f, a⟩; rfl

noncomputable instance : Primcodable CubeSymmetry := Primcodable.ofEquiv _ symmetryEquiv

theorem symmetry_data_primrec : Primrec symmetryEquiv := Primrec.of_equiv

theorem cubeSymmetry_act_primrec : Primrec₂ CubeSymmetry.act := by
  have planar : Primrec (fun a : CubeSymmetry × Voxel => a.1.planar.act a.2.1) :=
    squareSymmetry_act_primrec.comp (Primrec.fst.comp (symmetry_data_primrec.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have z : Primrec (fun a : CubeSymmetry × Voxel => if a.1.flip then -a.2.2 else a.2.2) := by
    apply (Primrec.cond
      (Primrec.fst.comp (Primrec.snd.comp (symmetry_data_primrec.comp Primrec.fst)))
      (int_negate_primrec.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).of_eq
    intro a
    cases hf : a.1.flip <;> simp [symmetryEquiv, hf]
  have axis : Primrec (fun a : CubeSymmetry × Voxel => a.1.axis) :=
    Primrec.snd.comp (Primrec.snd.comp (symmetry_data_primrec.comp Primrec.fst))
  apply (Primrec.ite (Primrec.eq.comp axis (Primrec.const 0)) (Primrec.pair planar z)
    (Primrec.ite (Primrec.eq.comp axis (Primrec.const 1))
      (Primrec.pair (Primrec.pair z (Primrec.fst.comp planar)) (Primrec.snd.comp planar))
      (Primrec.pair (Primrec.pair (Primrec.snd.comp planar) z) (Primrec.fst.comp planar)))).of_eq
  intro a
  rcases a with ⟨⟨p, f, axis⟩, c⟩
  fin_cases axis <;> rfl

theorem voxel_add_primrec : Primrec₂ Voxel.add :=
  Primrec.pair (cell_add_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (int_add_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem voxel_sub_primrec : Primrec₂ Voxel.sub :=
  Primrec.pair (cell_sub_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (int_subtract_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem boxVoxelList_primrec : Primrec boxVoxelList :=
  Primrec.list_flatMap TrominoAssignment.boxCellList_primrec
    (Primrec.list_map (TrominoAssignment.boxCellList_primrec.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))

def placementEquiv : VoxelPlacement Bool ≃ Bool × CubeSymmetry × Voxel where
  toFun p := (p.kind, p.symmetry, p.offset)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨k, s, c⟩; rfl

noncomputable instance : Primcodable (VoxelPlacement Bool) :=
  Primcodable.ofEquiv _ placementEquiv

theorem placement_data_primrec : Primrec placementEquiv := Primrec.of_equiv

theorem placement_mk_primrec : Primrec placementEquiv.symm := Primrec.of_equiv_symm

theorem kind_primrec : Primrec (VoxelPlacement.kind : VoxelPlacement Bool → Bool) :=
  Primrec.fst.comp placement_data_primrec

theorem symmetry_primrec : Primrec (VoxelPlacement.symmetry : VoxelPlacement Bool → CubeSymmetry) :=
  Primrec.fst.comp (Primrec.snd.comp placement_data_primrec)

theorem offset_primrec : Primrec (VoxelPlacement.offset : VoxelPlacement Bool → Voxel) :=
  Primrec.snd.comp (Primrec.snd.comp placement_data_primrec)

theorem tileList_primrec : Primrec₂ tileList := by
  apply (Primrec.cond Primrec.snd (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)).of_eq
  intro a
  cases a.2 <;> rfl

theorem candidates_primrec : Primrec₂ candidates := by
  have bySymmetry : Primrec₂ (fun (a : (Input × Voxel) × Bool) (s : CubeSymmetry) =>
      (tileList a.1.1 a.2).map (fun q => (⟨a.2, s, Voxel.sub a.1.2 (s.act q)⟩ : VoxelPlacement Bool))) := by
    apply Primrec.list_map (tileList_primrec.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
    change Primrec (fun a : (((Input × Voxel) × Bool) × CubeSymmetry) × Voxel =>
      placementEquiv.symm (a.1.1.2, a.1.2, Voxel.sub a.1.1.1.2 (a.1.2.act a.2)))
    exact placement_mk_primrec.comp (Primrec.pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (voxel_sub_primrec.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (cubeSymmetry_act_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))))
  exact Primrec.list_flatMap (Primrec.const [false, true])
    (Primrec.list_flatMap (Primrec.const symmetryList) bySymmetry)

theorem pool_primrec : Primrec₂ pool :=
  Primrec.list_flatMap (boxVoxelList_primrec.comp Primrec.snd)
    (candidates_primrec.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

open PlaneTilingSearch (subsets_primrec)

abbrev CoverInput := Input × VoxelPlacement Bool × Voxel

theorem covers_primrec : PrimrecPred (fun a : CoverInput => a.2.2 ∈ a.2.1.cells (tiles a.1)) := by
  have hit : PrimrecRel (fun (q : Voxel) (a : CoverInput) =>
      Voxel.add a.2.1.offset (a.2.1.symmetry.act q) = a.2.2) :=
    Primrec.eq.comp₂
      (voxel_add_primrec.comp₂
        (offset_primrec.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right)))
        (cubeSymmetry_act_primrec.comp₂
          (symmetry_primrec.comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.right))) Primrec₂.left))
      (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.right))
  apply (hit.exists_mem_list.comp
    (tileList_primrec.comp Primrec.fst (kind_primrec.comp (Primrec.fst.comp Primrec.snd))) Primrec.id).of_eq
  intro a
  simp only [VoxelPlacement.mem_cells_iff, tiles, List.mem_toFinset, id_eq]

abbrev ChoiceInput := Input × Voxel × List (VoxelPlacement Bool)

set_option maxHeartbeats 1000000 in
theorem valid_cell_primrec : PrimrecPred (fun a : ChoiceInput =>
    ∃ p ∈ a.2.2, a.2.1 ∈ p.cells (tiles a.1) ∧
      ∀ q ∈ a.2.2, a.2.1 ∈ q.cells (tiles a.1) → q = p) := by
  have others : PrimrecRel (fun (q : VoxelPlacement Bool) (a : Input × Voxel × VoxelPlacement Bool) =>
      a.2.1 ∈ q.cells (tiles a.1) → q = a.2.2) := by
    apply ((covers_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))).not.or
        (Primrec.eq.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).of_eq
    intro a
    tauto
  have chosen : PrimrecRel (fun (p : VoxelPlacement Bool) (a : ChoiceInput) =>
      a.2.1 ∈ p.cells (tiles a.1) ∧
        ∀ q ∈ a.2.2, a.2.1 ∈ q.cells (tiles a.1) → q = p) := by
    have cover : PrimrecPred (fun a : VoxelPlacement Bool × ChoiceInput =>
        a.2.2.1 ∈ a.1.cells (tiles a.2.1)) :=
      covers_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    have selected : Primrec (fun a : VoxelPlacement Bool × ChoiceInput => a.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have context : Primrec (fun a : VoxelPlacement Bool × ChoiceInput => (a.2.1, a.2.2.1, a.1)) :=
      Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
    have unique : PrimrecPred (fun a : VoxelPlacement Bool × ChoiceInput =>
        ∀ q ∈ a.2.2.2, a.2.2.1 ∈ q.cells (tiles a.2.1) → q = a.1) := by
      exact (others.forall_mem_list.comp selected context).of_eq (fun _ => Iff.rfl)
    exact cover.and unique
  exact chosen.exists_mem_list.comp (Primrec.snd.comp Primrec.snd) Primrec.id

variable (region : Set Voxel) (regionPR : PrimrecPred (fun c => c ∈ region))

theorem empty_cell_primrec : PrimrecPred (fun a : ChoiceInput =>
    ∀ p ∈ a.2.2, a.2.1 ∉ p.cells (tiles a.1)) := by
  have absent : PrimrecRel (fun (p : VoxelPlacement Bool) (a : ChoiceInput) =>
      a.2.1 ∉ p.cells (tiles a.1)) :=
    (covers_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))).not
  exact absent.forall_mem_list.comp (Primrec.snd.comp Primrec.snd) Primrec.id

include regionPR

theorem region_cell_primrec : PrimrecPred (fun a : ChoiceInput =>
    if a.2.1 ∈ region then
      ∃ p ∈ a.2.2, a.2.1 ∈ p.cells (tiles a.1) ∧
        ∀ q ∈ a.2.2, a.2.1 ∈ q.cells (tiles a.1) → q = p
    else ∀ p ∈ a.2.2, a.2.1 ∉ p.cells (tiles a.1)) := by
  have inside : PrimrecPred (fun a : ChoiceInput => a.2.1 ∈ region) :=
    regionPR.comp (Primrec.fst.comp Primrec.snd)
  apply ((inside.and valid_cell_primrec).or (inside.not.and empty_cell_primrec)).of_eq
  intro a
  by_cases h : a.2.1 ∈ region <;> simp only [h, ↓reduceIte, true_and, false_and,
    not_true_eq_false, not_false_eq_true, false_or, or_false]

theorem valid_primrec : PrimrecPred (fun a : Input × Nat × List (VoxelPlacement Bool) =>
    Valid a.1 region a.2.1 a.2.2) := by
  have cells : PrimrecRel (fun (c : Voxel) (a : Input × Nat × List (VoxelPlacement Bool)) =>
      if c ∈ region then
        ∃ p ∈ a.2.2, c ∈ p.cells (tiles a.1) ∧
          ∀ q ∈ a.2.2, c ∈ q.cells (tiles a.1) → q = p
      else ∀ p ∈ a.2.2, c ∉ p.cells (tiles a.1)) :=
    (region_cell_primrec region regionPR).comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  exact cells.forall_mem_list.comp
    (boxVoxelList_primrec.comp (Primrec.fst.comp Primrec.snd)) Primrec.id

theorem finiteSearch_primrec : PrimrecRel (fun input radius => FiniteSearch input region radius) := by
  have selected : PrimrecRel (fun (ps : List (VoxelPlacement Bool)) (a : Input × Nat) =>
      Valid a.1 region a.2 ps) :=
    (valid_primrec region regionPR).comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst))
  exact selected.exists_mem_list.comp (subsets_primrec.comp pool_primrec) Primrec.id

theorem coRE : LeanWang.CoREPred (fun input => VoxelTileable (tiles input) region) := by
  have obstruction := LeanWang.REPred.exists_nat
    (p := fun input radius => ¬ FiniteSearch input region radius)
    (finiteSearch_primrec region regionPR).not.computablePred
  exact obstruction.of_eq (fun input => by
    change (∃ r, ¬ FiniteSearch input region r) ↔ ¬ VoxelTileable (tiles input) region
    rw [tileable_iff]
    exact not_forall.symm)

end LeanTrominoes.VoxelTilingSearch
