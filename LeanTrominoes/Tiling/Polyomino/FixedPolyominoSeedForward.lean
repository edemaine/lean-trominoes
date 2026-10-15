/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedVertexCorrectness

/-! # Satisfying prescribed matching bits extend to the actual fixed P/Q pair -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed.VertexEncoding
open PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder
attribute [local irreducible] sourcePeriod coarsePeriod tilePeriod
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance
attribute [local irreducible] FixedNormalizedOrientationSeed.fixedDrawing

theorem prescribed_vertices (base : Cell) (seed : MatchingSeed) (supported : Supported seed)
    (completed : Prescribed FixedPlanarThreeDMSeed.fixedInstance.Satisfies seed) :
    CanonicalISelection.Prescribed drawing (vertexPins base seed) := by
  obtain ⟨matching,valid,pins⟩ := completed
  obtain ⟨a,ha,inverse⟩ := (PeriodicThreeDM.SeedNormalization.boundedSeedFactor
    FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance_degree
    FixedPlanarThreeDMSeed.fixedPresentation_collisionFree).complete matching
      ((PeriodicThreeDM.SeedNormalization.formula_satisfies_iff matching).2 valid)
  have drawingEqual : PeriodicThreeDM.SeedNormalization.drawing presentation = drawing := by
    unfold PeriodicThreeDM.SeedNormalization.drawing FixedPolyominoSeed.drawing
      FixedNormalizedOrientationSeed.fixedDrawing FixedPolyominoSeed.presentation
    rfl
  rw [drawingEqual] at ha
  let shifted := PeriodicCNF.Translation.assignment base a
  have shiftedValid : (PeriodicCNF.Reflection.formula (NormalizedOrientation.AsCNF.formula drawing)).Satisfies shifted :=
    PeriodicCNF.Translation.satisfies base _ a ha
  let inward := NormalizedOrientation.AsCNF.orientation drawing (PeriodicCNF.Reflection.assignment shifted)
  have oriented : drawing.IsOrientation inward :=
    (NormalizedOrientation.AsCNF.satisfies_iff drawing _).1
      ((PeriodicCNF.Reflection.satisfies_iff (NormalizedOrientation.AsCNF.formula drawing) shifted).1 shiftedValid)
  refine ⟨inward,oriented,?_⟩
  intro vertex member
  unfold vertexPins at member
  obtain ⟨pin,pinMember,rfl⟩ := List.mem_map.mp member
  have bound := supported pin pinMember
  have decoded : decode (PeriodicThreeDM.SeedNormalization.boundedRead presentation) shifted
      pin.1.1 (Cell.add base pin.1.2) = pin.2 := by
    rw [PeriodicCNF.Translation.decode,PeriodicCNF.Translation.at_shift]
    exact (inverse pin.1.1 bound pin.1.2).trans (pins pin pinMember)
  have readSame : decode (PeriodicThreeDM.SeedNormalization.read presentation) shifted
      pin.1.1 (Cell.add base pin.1.2) = pin.2 := by
    simpa only [decode,PeriodicThreeDM.SeedNormalization.boundedRead_eq presentation pin.1.1 bound] using decoded
  rw [PeriodicThreeDM.SeedNormalization.read_decode] at readSame
  rw [drawingEqual] at readSame
  change (!(inward (presentation.endpointDrawingLocation
    (PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) pin.1.1)
    (Cell.add base pin.1.2))
    ((PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) pin.1.1).finalNormalizedPort presentation).side) : Bool) = pin.2 at readSame
  rw [← location_eq pin.1.1 bound] at readSame
  have constraint := oriented.1 (location pin.1.1 (Cell.add base pin.1.2))
  rw [vertex_type pin.1.1 bound] at constraint
  change inward _ .west = inward _ .north ∧ inward _ .north = inward _ .east at constraint
  have same : inward (location pin.1.1 (Cell.add base pin.1.2))
      ((PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) pin.1.1).finalNormalizedPort presentation).side = inward (location pin.1.1 (Cell.add base pin.1.2)) .north := by
    cases (PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) pin.1.1).finalNormalizedPort presentation with
    | west => exact constraint.1
    | north => rfl
    | east => exact constraint.2.symm
  rw [same] at readSame
  have result := congrArg Bool.not readSame
  simpa only [Bool.not_not] using result

theorem forward (base : Cell) (seed : MatchingSeed) (supported : Supported seed)
    (completed : Prescribed FixedPlanarThreeDMSeed.fixedInstance.Satisfies seed) :
    Problem (referencePlacement :: placements base seed) := by
  obtain ⟨coarse,tiling,retained⟩ := CanonicalISelection.prescribed_tiling drawing
    FixedNormalizedOrientationSeed.fixedDrawing_wellFormed (vertexPins base seed)
    (checked base seed supported) (prescribed_vertices base seed supported completed)
  have shifted := tiling.recenter_region (latticeBlockOrigin (9,3))
  let shiftedPlacements : Set (Placement Unit) := {p | p.shift (latticeBlockOrigin (9,3)) ∈ coarse}
  have refined : IsTiling (fun _ : Unit => bumpy) (holesRegion tilePeriod fixedHoles)
      (expandPlacement '' shiftedPlacements) := by
    rw [fixedHoles_carrier]
    exact expand_tiling _ (ShiftedGadgetReadout.original drawing (9,3)) shiftedPlacements shifted
  let mixed := pairPlacements (expandPlacement '' shiftedPlacements) (gridPlacements tilePeriod)
  apply (problem_iff _).2
  refine ⟨mixed,isTiling_pair_of_complement bumpy largeTile (holesRegion tilePeriod fixedHoles)
    _ _ refined (grid_tiling (by have := tilePeriod_large; omega) fixedHoles),?_⟩
  intro p member
  rcases List.mem_cons.mp member with rfl | member
  · change referencePlacement.untag ∈ gridPlacements tilePeriod
    exact ⟨rfl,0,0,by simp [referencePlacement,Placement.untag]⟩
  · unfold placements at member
    obtain ⟨p,pMember,rfl⟩ := List.mem_map.mp member
    change ((expandPlacement (p.shift (ShiftedGadgetReadout.inverseOffset (9,3)))).tag false).untag ∈
      expandPlacement '' shiftedPlacements
    rw [Placement.untag_tag]
    refine ⟨p.shift (ShiftedGadgetReadout.inverseOffset (9,3)),?_,rfl⟩
    change (p.shift (Cell.sub (0,0) (latticeBlockOrigin (9,3)))).shift (latticeBlockOrigin (9,3)) ∈ coarse
    rw [Placement.shift_cancel]
    exact retained p pMember

end LeanTrominoes.FixedPolyominoSeed.VertexEncoding
