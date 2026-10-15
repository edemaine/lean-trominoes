/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.KeyedComplementQuadrantRecovery
import LeanTrominoes.Tiling.Tromino.BumpyTrominoRefinement
import Lean.Util.CollectAxioms

/-! # Retaining a partial I-tiling and its pins in the forced quadrant -/
namespace LeanTrominoes.KeyedPeriodicComplement
open PlusRefinement
set_option maxHeartbeats 800000

private theorem bumpy_cells_near (p : Placement Unit) {c d : Cell}
    (hc : c ∈ p.cells (fun _ => bumpy)) (hd : d ∈ p.cells (fun _ => bumpy)) :
    c.1-14 ≤ d.1 ∧ d.2 ≤ c.2+14 := by
  have bounds : ∀ u ∈ bumpy, -7 ≤ u.1 ∧ u.1 ≤ 7 ∧ -7 ≤ u.2 ∧ u.2 ≤ 7 := by decide
  rcases c with ⟨cx,cy⟩; rcases d with ⟨dx,dy⟩
  obtain ⟨first,firstMember,firstEq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
  obtain ⟨second,secondMember,secondEq⟩ := (Placement.mem_cells_iff _ _ _).mp hd
  have firstBounds := bounds first firstMember
  have secondBounds := bounds second secondMember
  rcases first with ⟨fx,fy⟩; rcases second with ⟨sx,sy⟩
  rcases p with ⟨kind,symmetry,px,py⟩
  cases symmetry <;> simp only [SquareSymmetry.act,Cell.add,Prod.mk.injEq] at firstEq secondEq <;>
    dsimp at firstBounds secondBounds ⊢ <;> omega

theorem deep_P_inside_refinement {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = region original)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) {c : Cell}
    (right : (n : Int)+14 ≤ c.1) (above : c.2 ≤ -(n : Int)-14)
    (p : Placement Unit) (member : p.tag false ∈ ps)
    (cover : c ∈ p.cells (fun _ => bumpy)) :
    ∀ d ∈ p.cells (fun _ => bumpy), d ∈ region original := by
  intro d dMember
  rw [← carrier]
  by_contra outside
  have near := bumpy_cells_near p cover dMember
  have canonical := grid_tiling (by omega : 0 < n) holes
  obtain ⟨q,qMember,qCover⟩ := canonical.exists_cover outside
  have forced := canonical_cover_in_forced_quadrant hn period holes admissible ps tiling seed
    (c := d) (by omega) (by omega) qMember qCover
  have different : p.tag false ≠ q.tag true := by
    intro equal
    have kinds := congrArg Placement.kind equal
    simp [Placement.tag] at kinds
  exact (Finset.disjoint_left.mp (tiling.disjoint_cells member forced different)) dMember qCover

/-- All recovered coarse placements stay within the original region. This
set is defined from the original mixed tiling, so prescribed placements are
retained literally. -/
def recoveredCoarse (original : Set Cell) (ps : Set (Placement Bool)) : Set (Placement Unit) :=
  {p | (expandPlacement p).tag false ∈ ps ∧
    ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ original}

theorem recoveredCoarse_pin (original : Set Cell) (ps : Set (Placement Bool))
    (p : Placement Unit) (pin : (expandPlacement p).tag false ∈ ps)
    (inside : ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ original) :
    p ∈ recoveredCoarse original ps := ⟨pin,inside⟩

private theorem covers_center (p : Placement Unit) {c : Cell}
    (cover : c ∈ p.cells (fun _ => Tromino.I.cells)) :
    pixel c (0,0) ∈ (expandPlacement p).cells (fun _ => bumpy) :=
  (mem_expanded_cells _ _ _).mpr ⟨c,cover,_,by decide,rfl⟩

/-- The recovered coarse placements cover every original cell sufficiently
far inside the forced quadrant exactly once. -/
theorem recoveredCoarse_uniqueCover {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = region original)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) {c : Cell} (inside : c ∈ original)
    (right : (n : Int)+4 ≤ c.1) (above : c.2 ≤ -(n : Int)-4) :
    ∃! p : Placement Unit,
      p ∈ recoveredCoarse original ps ∧ c ∈ p.cells (fun _ => Tromino.I.cells) := by
  have hole : pixel c (0,0) ∈ region original := ⟨c,inside,_,by decide,rfl⟩
  have right' : 3*(n : Int)+12 ≤ (pixel c (0,0)).1 := by dsimp [pixel,Cell.add,Cell.scale]; omega
  have above' : (pixel c (0,0)).2 ≤ -3*(n : Int)-12 := by dsimp [pixel,Cell.add,Cell.scale]; omega
  obtain ⟨p,⟨member,cover⟩,unique⟩ := unique_P_at_deep_hole hn period holes admissible original
    carrier ps tiling seed hole right' above'
  have contained := deep_P_inside_refinement hn period holes admissible original carrier ps tiling seed
    (by omega : (n : Int)+14 ≤ (pixel c (0,0)).1)
    (by omega : (pixel c (0,0)).2 ≤ -(n : Int)-14) p member cover
  have aligned := bumpy_placement_aligned p original contained
  have expanded := expand_contract p aligned
  have coarseCover : c ∈ (contractPlacement p).cells (fun _ => Tromino.I.cells) := by
    rw [← expanded] at cover
    obtain ⟨other,otherCover,subcell,subcellMember,equal⟩ := (mem_expanded_cells _ _ _).mp cover
    obtain ⟨rfl,_⟩ := pixel_injective subcellMember (show (0,0) ∈ cross by decide) equal
    exact otherCover
  have coarseInside : ∀ d ∈ (contractPlacement p).cells (fun _ => Tromino.I.cells), d ∈ original := by
    intro d dCover
    have refinedCover := covers_center _ dCover
    rw [expanded] at refinedCover
    obtain ⟨other,otherInside,subcell,subcellMember,equal⟩ := contained _ refinedCover
    obtain ⟨rfl,_⟩ := pixel_injective subcellMember (show (0,0) ∈ cross by decide) equal
    exact otherInside
  refine ⟨contractPlacement p,⟨⟨by rwa [expanded],coarseInside⟩,coarseCover⟩,?_⟩
  rintro other ⟨otherMember,otherCover⟩
  apply expandPlacement_injective
  rw [expanded]
  exact unique (expandPlacement other) ⟨otherMember.1,covers_center other otherCover⟩

theorem recoveredCoarse_disjoint (original : Set Cell) (ps : Set (Placement Bool))
    {q : Polyomino} (tiling : IsTiling (pairTiles bumpy q) Set.univ ps)
    {first second : Placement Unit} (firstMember : first ∈ recoveredCoarse original ps)
    (secondMember : second ∈ recoveredCoarse original ps) (different : first ≠ second) :
    Disjoint (first.cells (fun _ => Tromino.I.cells)) (second.cells (fun _ => Tromino.I.cells)) := by
  apply Finset.disjoint_left.mpr
  intro c firstCover secondCover
  have different' : (expandPlacement first).tag false ≠ (expandPlacement second).tag false := by
    intro equal
    apply different
    apply expandPlacement_injective
    simpa using congrArg Placement.untag equal
  exact (Finset.disjoint_left.mp (tiling.disjoint_cells firstMember.1 secondMember.1 different'))
    (covers_center first firstCover) (covers_center second secondCover)

open Lean Elab Command in
run_cmd do
  let name := ``recoveredCoarse_uniqueCover
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement
