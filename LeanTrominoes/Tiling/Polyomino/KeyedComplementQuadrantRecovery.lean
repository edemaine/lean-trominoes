/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.KeyedComplementPropagation
import LeanTrominoes.Tiling.Polyomino.KeyedComplementRefinedExclusion
import Mathlib.Tactic.Linarith
import Lean.Util.CollectAxioms

/-! # Recovering holes inside the forced Q quadrant

These statements concern the original mixed tiling containing the prescribed
Q tile. They require no recentering or replacement by a compactness limit.
-/
namespace LeanTrominoes.KeyedPeriodicComplement
set_option maxHeartbeats 800000

theorem canonical_cover_in_forced_quadrant {n : Nat} (hn : 96 ≤ n)
    (period : (n : Int) % 3 = 0) (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) {c : Cell}
    (right : (n : Int) ≤ c.1) (above : c.2 ≤ -(n : Int))
    {q : Placement Unit} (grid : q ∈ gridPlacements n)
    (cover : c ∈ q.cells (fun _ => tile n holes)) : q.tag true ∈ ps := by
  rcases grid with ⟨symmetry,i,j,offset⟩
  obtain ⟨source,sourceMember,sourceEq⟩ := (Placement.mem_cells_iff _ _ _).mp cover
  have bounds := tile_bounds n holes sourceMember
  have coords := sourceEq
  have xcoord := congrArg Prod.fst coords
  have ycoord := congrArg Prod.snd coords
  simp only [symmetry,offset,SquareSymmetry.act,Cell.add] at xcoord ycoord
  have ni : (0 : Int) ≤ i := by
    have positive : (0 : Int) < n := by omega
    nlinarith [xcoord]
  have nj : j ≤ (0 : Int) := by
    have positive : (0 : Int) < n := by omega
    nlinarith [ycoord]
  have icast : (i.toNat : Int) = i := by omega
  have jcast : ((-j).toNat : Int) = -j := by omega
  have forced := quadrant_placements hn period holes admissible ps tiling (0,0) seed i.toNat (-j).toNat
  have equal : q.tag true =
      (⟨true,.identity,Cell.add (0,0) ((n : Int)*i.toNat,-(n : Int)*(-j).toNat)⟩ : Placement Bool) := by
    apply Placement.ext
    · rfl
    · exact symmetry
    · simp [Placement.tag,offset,Cell.add,icast,jcast]
  rwa [equal]

private theorem tile_cells_near {n : Nat} (_hn : 96 ≤ n) (holes : Polyomino)
    (p : Placement Unit) {c d : Cell}
    (hc : c ∈ p.cells (fun _ => tile n holes))
    (hd : d ∈ p.cells (fun _ => tile n holes)) :
    c.1 - 2*((n : Int)+4) ≤ d.1 ∧ d.2 ≤ c.2 + 2*((n : Int)+4) := by
  rcases c with ⟨cx,cy⟩; rcases d with ⟨dx,dy⟩
  obtain ⟨first,firstMember,firstEq⟩ := (Placement.mem_cells_iff _ _ _).mp hc
  obtain ⟨second,secondMember,secondEq⟩ := (Placement.mem_cells_iff _ _ _).mp hd
  have firstBounds := tile_bounds n holes firstMember
  have secondBounds := tile_bounds n holes secondMember
  rcases first with ⟨fx,fy⟩; rcases second with ⟨sx,sy⟩
  rcases p with ⟨kind,symmetry,px,py⟩
  cases symmetry <;> simp only [SquareSymmetry.act,Cell.add,Prod.mk.injEq] at firstEq secondEq <;>
    dsimp at firstBounds secondBounds ⊢ <;> omega

/-- No Q placement covers a refined-hole cell far enough inside the quadrant
forced by the prescribed Q at the origin. -/
theorem no_Q_at_deep_hole {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = PlusRefinement.region original)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) {c : Cell}
    (hole : c ∈ PlusRefinement.region original)
    (right : 3*(n : Int)+12 ≤ c.1) (above : c.2 ≤ -3*(n : Int)-12)
    (p : Placement Unit) (member : p.tag true ∈ ps) :
    c ∉ p.cells (fun _ => tile n holes) := by
  intro cover
  apply tile_not_inside_refinement hn holes admissible original p
  intro d dMember
  rw [← carrier]
  by_contra outside
  have near := tile_cells_near hn holes p cover dMember
  have canonical := grid_tiling (by omega : 0 < n) holes
  obtain ⟨q,qMember,qCover⟩ := canonical.exists_cover outside
  have forced := canonical_cover_in_forced_quadrant hn period holes admissible ps tiling seed
    (c := d) (by omega) (by omega) qMember qCover
  have different : p.tag true ≠ q.tag true := by
    intro equal
    have placementsEqual : p = q := by
      have h := congrArg Placement.untag equal
      simpa using h
    subst p
    have pOutside := canonical.tilesInside q qMember c cover
    rw [carrier] at pOutside
    exact pOutside hole
  have disjoint := tiling.disjoint_cells member forced different
  exact (Finset.disjoint_left.mp disjoint) dMember qCover

/-- A deep hole has a unique covering P in the same mixed tiling. -/
theorem unique_P_at_deep_hole {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = PlusRefinement.region original)
    (ps : Set (Placement Bool))
    (tiling : IsTiling (pairTiles PlusRefinement.bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) {c : Cell}
    (hole : c ∈ PlusRefinement.region original)
    (right : 3*(n : Int)+12 ≤ c.1) (above : c.2 ≤ -3*(n : Int)-12) :
    ∃! p : Placement Unit, p.tag false ∈ ps ∧ c ∈ p.cells (fun _ => PlusRefinement.bumpy) := by
  obtain ⟨a,⟨member,cover⟩,unique⟩ := tiling.uniqueCover c (Set.mem_univ c)
  cases kind : a.kind with
  | false =>
      have tagged : a.untag.tag false = a := by rw [← kind,Placement.tag_untag]
      have pCover : c ∈ a.untag.cells (fun _ => PlusRefinement.bumpy) := by
        simpa [Placement.cells,Placement.untag,pairTiles,kind] using cover
      refine ⟨a.untag,⟨by rwa [tagged],pCover⟩,?_⟩
      rintro other ⟨otherMember,otherCover⟩
      have equal := unique (other.tag false) ⟨otherMember,otherCover⟩
      simpa only [Placement.untag_tag] using congrArg Placement.untag equal
  | true =>
      have tagged : a.untag.tag true = a := by rw [← kind,Placement.tag_untag]
      have qCover : c ∈ a.untag.cells (fun _ => tile n holes) := by
        simpa [Placement.cells,Placement.untag,pairTiles,kind] using cover
      exact False.elim (no_Q_at_deep_hole hn period holes admissible original carrier ps tiling seed
        hole right above a.untag (by rwa [tagged]) qCover)

open Lean Elab Command in
run_cmd do
  let name := ``unique_P_at_deep_hole
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement
