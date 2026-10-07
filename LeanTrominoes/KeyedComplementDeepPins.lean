/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementGadgetPins

/-! # Deep prescribed P placements automatically lie in the recovered region -/
namespace LeanTrominoes.KeyedPeriodicComplement
open PlusRefinement Gadget
attribute [local irreducible] localAssignmentFromGlobal
attribute [local irreducible] admissibleCandidates windowCandidates exactCellTilings

theorem deep_coarse_pin_inside {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (original : Set Cell) (carrier : holesRegion n holes = region original)
    (ps : Set (Placement Bool))
    (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) (p : Placement Unit)
    (pin : (expandPlacement p).tag false ∈ ps) {c : Cell}
    (cover : c ∈ p.cells (fun _ => Tromino.I.cells))
    (right : (n : Int)+4 ≤ c.1) (above : c.2 ≤ -(n : Int)-4) :
    ∀ d ∈ p.cells (fun _ => Tromino.I.cells), d ∈ original := by
  have centerCover : pixel c (0,0) ∈ (expandPlacement p).cells (fun _ => bumpy) :=
    (mem_expanded_cells _ _ _).2 ⟨c,cover,_,by decide,rfl⟩
  have bounds : (n : Int)+14 ≤ (pixel c (0,0)).1 ∧
      (pixel c (0,0)).2 ≤ -(n : Int)-14 := by
    dsimp [pixel,Cell.add,Cell.scale]
    omega
  have inside := deep_P_inside_refinement hn period holes admissible original carrier ps tiling seed
    bounds.1 bounds.2 (expandPlacement p) pin centerCover
  intro d hd
  have refined := inside (pixel d (0,0)) ((mem_expanded_cells _ _ _).2 ⟨d,hd,_,by decide,rfl⟩)
  obtain ⟨other,otherInside,subcell,subcellMember,equal⟩ := refined
  obtain ⟨rfl,_⟩ := pixel_injective subcellMember (show (0,0) ∈ cross by decide) equal
  exact otherInside

namespace PartialGadgetReadout

theorem readout_eq_of_deep_pins {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (drawing : PeriodicOrthogonalDrawing)
    (carrier : holesRegion n holes = region (drawing.periodicRegion .I).carrier)
    (ps : Set (Placement Bool))
    (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) (cell : Cell) (safe : Deep n 0 cell)
    (pattern : Finset (Placement Unit))
    (valid : pattern ∈ exactCellTilings .I (drawing.getAt cell))
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      (expandPlacement p).tag false ∈ ps) :
    readout drawing ps cell = iConfigurationInward (drawing.getAt cell)
      (portConfiguration .I (orthogonalCellGadget .I (drawing.getAt cell)) pattern) := by
  have localValid := (mem_exactCellTilings_iff _ _ _).1 valid
  have translated : IsWindowTiling .I (latticeBlockWindow cell)
      (drawingBlockRegion .I drawing cell) (translatePlacements (latticeBlockOrigin cell) pattern) := by
    simpa only [latticeBlockWindow,drawingBlockRegion,latticeBlockRegion,
      orthogonalCellGadget,paperGadget,Gadget.window,Gadget.region] using
      localValid.translate (latticeBlockOrigin cell)
  apply readout_eq_of_pins drawing ps tiling cell pattern localValid
  · intro p member
    have candidate : p ∈ admissibleCandidates .I (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell) :=
      translated.1 member
    obtain ⟨c,hc,cover⟩ := ((mem_admissibleCandidates_iff .I
      (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell) p).1 candidate).1
    have bounds := window_deep safe c hc
    exact deep_coarse_pin_inside hn period holes admissible _ carrier ps tiling seed p
      (pins p member) cover bounds.1 bounds.2
  · exact pins

end PartialGadgetReadout
end LeanTrominoes.KeyedPeriodicComplement
