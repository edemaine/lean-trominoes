/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPolyominoSeedMargin
import LeanTrominoes.PeriodicCNFTranslation

/-! # The emitted P patterns retain their matching-bit values -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed.VertexEncoding
open PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder
attribute [local irreducible] sourcePeriod coarsePeriod tilePeriod
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance
attribute [local irreducible] ShiftedGadgetReadout.assignment ShiftedGadgetReadout.readout
attribute [local irreducible] CanonicalISelection.trichromaticPattern

theorem matching_decode (ps : Set (Placement Bool)) (index : Nat)
    (bound : index < FixedPlanarThreeDMSeed.fixedInstance.triples.length) (c : Cell) :
    decode (PeriodicThreeDM.SeedNormalization.boundedRead presentation)
      (ShiftedGadgetReadout.assignment drawing (9,3) ps) index c =
      !(ShiftedGadgetReadout.readout drawing (9,3) ps (location index c)
        ((PeriodicThreeDM.SeedNormalization.selectedEndpoint
          (problem := FixedPlanarThreeDMSeed.fixedInstance) index).finalNormalizedPort presentation).side) := by
  have equal : decode (PeriodicThreeDM.SeedNormalization.boundedRead presentation)
      (ShiftedGadgetReadout.assignment drawing (9,3) ps) index c =
      decode (PeriodicThreeDM.SeedNormalization.read presentation)
        (ShiftedGadgetReadout.assignment drawing (9,3) ps) index c := by
    simp only [decode,PeriodicThreeDM.SeedNormalization.boundedRead_eq presentation index bound]
  rw [equal,PeriodicThreeDM.SeedNormalization.read_decode]
  unfold ShiftedGadgetReadout.assignment
  rw [PeriodicCNF.Reflection.assignment_assignment,
    show PeriodicThreeDM.SeedNormalization.drawing presentation = drawing from rfl,
    NormalizedOrientation.AsCNF.orientation_assignment]
  rw [location_eq index bound c]
  rfl

theorem matching_pin (seed : MatchingSeed) (supported : Supported seed)
    (ps : Set (Placement Bool)) (tiling : IsTiling (pairTiles bumpy largeTile) Set.univ ps)
    (qSeed : referencePlacement ∈ ps)
    (retained : ∀ p ∈ placements (AugmentedSoundness.baseline (seedMargin seed)) seed, p ∈ ps)
    (pin : Pin) (member : pin ∈ seed) :
    decode (PeriodicThreeDM.SeedNormalization.boundedRead presentation)
      (ShiftedGadgetReadout.assignment drawing (9,3) ps) pin.1.1
      (Cell.add (AugmentedSoundness.baseline (seedMargin seed)) pin.1.2) = pin.2 := by
  rw [matching_decode ps pin.1.1 (supported pin member)]
  have forced := ShiftedGadgetReadout.readout_eq_of_deep_pins tilePeriod_large tilePeriod_divisible
    fixedHoles fixedHoles_admissible drawing (9,3) fixedHoles_carrier ps tiling qSeed
    (location pin.1.1 (Cell.add (AugmentedSoundness.baseline (seedMargin seed)) pin.1.2))
    (seed_deep seed pin member) (CanonicalISelection.trichromaticPattern (order pin.1.1) (!pin.2))
    (by rw [vertex_type pin.1.1 (supported pin member)]; exact CanonicalISelection.trichromaticPattern_exact _ _)
    (by
      intro p hp
      obtain ⟨localP,localMember,rfl⟩ := Finset.mem_image.mp hp
      apply retained
      apply List.mem_map.mpr
      refine ⟨_,List.mem_flatMap.mpr ⟨
        ((location pin.1.1 (Cell.add (AugmentedSoundness.baseline (seedMargin seed)) pin.1.2),order pin.1.1),!pin.2),
        List.mem_map.mpr ⟨pin,member,rfl⟩,List.mem_map.mpr ⟨localP,Finset.mem_toList.mpr localMember,rfl⟩⟩,rfl⟩)
  rw [forced,vertex_type pin.1.1 (supported pin member),
    PeriodicThreeDM.SeedNormalization.trichromaticPattern_port_readout]
  exact Bool.not_not _

theorem problem_iff (seed : List (Placement Bool)) : Problem seed ↔
    ∃ ps, IsTiling (pairTiles bumpy largeTile) Set.univ ps ∧ ∀ p ∈ seed, p ∈ ps := by
  have tiles : PlaneTilingSearch.tiles (smallTile.toList,largeTile.toList) = pairTiles bumpy largeTile := by
    funext kind
    cases kind <;> simp only [PlaneTilingSearch.tiles,PlaneTilingSearch.tileList,smallTile,
      pairTiles,Bool.false_eq_true,ite_false,ite_true,Finset.toList_toFinset]
  simp only [Problem,FinitePolyominoCompletion.fixedProblem,FinitePolyominoCompletion.Completable,
    tiles]

end LeanTrominoes.FixedPolyominoSeed.VertexEncoding
