/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BumpyTrominoRefinement
import LeanTrominoes.PlaneTilingSearchComputability
import Lean.Util.CollectAxioms

/-! # Cross refinement preserves finite prescribed placements

The refinement equivalence is strengthened to retain the actual placements,
which is necessary when transferring a finite completion seed.
-/
namespace LeanTrominoes.PlusRefinement

theorem expand_tiling {K : Type} (tiles : K → Polyomino) (original : Set Cell)
    (placements : Set (Placement K)) (tiling : IsTiling tiles original placements) :
    IsTiling (fun k => polyomino (tiles k)) (region original) (expandPlacement '' placements) := by
  classical
  constructor
  · rintro _ ⟨p,hp,rfl⟩ c hc
    obtain ⟨parent,hparent,subcell,hu,rfl⟩ := (mem_expanded_cells _ _ _).mp hc
    exact ⟨parent,tiling.tilesInside p hp parent hparent,subcell,hu,rfl⟩
  · rintro c ⟨parent,hparent,subcell,hu,rfl⟩
    obtain ⟨p,⟨hp,hpc⟩,unique⟩ := tiling.uniqueCover parent hparent
    refine ⟨expandPlacement p,⟨⟨p,hp,rfl⟩,
      (mem_expanded_cells _ _ _).mpr ⟨parent,hpc,subcell,hu,rfl⟩⟩,?_⟩
    rintro q ⟨⟨other,ho,rfl⟩,hc⟩
    obtain ⟨otherParent,hop,otherSubcell,hou,he⟩ := (mem_expanded_cells _ _ _).mp hc
    obtain ⟨rfl,rfl⟩ := pixel_injective hou hu he
    exact congrArg expandPlacement (unique other ⟨ho,hop⟩)

theorem contract_tiling (original : Set Cell) (placements : Set (Placement Unit))
    (tiling : IsTiling (fun _ => bumpy) (region original) placements) :
    IsTiling (fun _ : Unit => Tromino.I.cells) original {p | expandPlacement p ∈ placements} := by
  classical
  have covers_center (p : Placement Unit) (parent : Cell)
      (hc : parent ∈ p.cells (fun _ => Tromino.I.cells)) :
      pixel parent (0,0) ∈ (expandPlacement p).cells (fun _ => bumpy) :=
    (mem_expanded_cells _ _ _).mpr ⟨parent,hc,_,by decide,rfl⟩
  constructor
  · intro p hp parent hc
    have inside := tiling.tilesInside (expandPlacement p) hp _ (covers_center p parent hc)
    obtain ⟨other,ho,subcell,hu,he⟩ := inside
    obtain ⟨rfl,_⟩ := pixel_injective hu (show (0,0) ∈ cross by decide) he
    exact ho
  · intro parent hp
    have refined : pixel parent (0,0) ∈ region original := ⟨parent,hp,_,by decide,rfl⟩
    obtain ⟨p,⟨hpmem,hpc⟩,unique⟩ := tiling.uniqueCover _ refined
    have aligned := bumpy_placement_aligned p original (tiling.tilesInside p hpmem)
    have ep := expand_contract p aligned
    have hcoarse : expandPlacement (contractPlacement p) ∈ placements := by rwa [ep]
    have hcell : parent ∈ (contractPlacement p).cells (fun _ => Tromino.I.cells) := by
      rw [← ep] at hpc
      obtain ⟨other,ho,subcell,hu,he⟩ := (mem_expanded_cells _ _ _).mp hpc
      obtain ⟨rfl,_⟩ := pixel_injective hu (show (0,0) ∈ cross by decide) he
      exact ho
    refine ⟨contractPlacement p,⟨hcoarse,hcell⟩,?_⟩
    rintro other ⟨ho,hc⟩
    apply expandPlacement_injective
    rw [ep]
    exact unique (expandPlacement other) ⟨ho,covers_center other parent hc⟩

def Seeded (shape : Polyomino) (original : Set Cell) (seed : List (Placement Unit)) : Prop :=
  ∃ placements, IsTiling (fun _ : Unit => shape) original placements ∧
    ∀ p ∈ seed, p ∈ placements

theorem seeded_refinement_iff (original : Set Cell) (seed : List (Placement Unit)) :
    Seeded bumpy (region original) (seed.map expandPlacement) ↔
      Seeded Tromino.I.cells original seed := by
  constructor
  · rintro ⟨placements,tiling,retained⟩
    refine ⟨{p | expandPlacement p ∈ placements},contract_tiling original placements tiling,?_⟩
    intro p hp
    exact retained _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · rintro ⟨placements,tiling,retained⟩
    refine ⟨expandPlacement '' placements,expand_tiling _ original placements tiling,?_⟩
    intro p hp
    obtain ⟨coarse,hc,rfl⟩ := List.mem_map.mp hp
    exact ⟨coarse,retained coarse hc,rfl⟩

theorem expandPlacement_primrec : Primrec (@expandPlacement Unit) := by
  open Computability TrominoAssignment in
  have constructor : Primrec placementUnitEquiv.symm := Primrec.of_equiv_symm
  apply (constructor.comp (Primrec.pair (Primrec.const ())
    (Primrec.pair placement_symmetry_primrec
      (cell_scale_primrec.comp (Primrec.const 3) placement_offset_primrec)))).of_eq
  intro p
  cases p with
  | mk kind symmetry offset => cases kind; rfl

theorem seed_refinement_primrec : Primrec (fun seed : List (Placement Unit) =>
    seed.map expandPlacement) :=
  Primrec.list_map Primrec.id (expandPlacement_primrec.comp Primrec.snd)

open Lean Elab Command in
run_cmd do
  let name := ``seeded_refinement_iff
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do
    throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PlusRefinement
