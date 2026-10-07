/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPolyominoAugmentedQuarterSoundness
import LeanTrominoes.PeriodicThreeDMNormalizationSeedVertices
import LeanTrominoes.KeyedComplementShiftedGadgetPins
import LeanTrominoes.GadgetICanonicalSeedComputability

/-! # Effective finite P patterns for prescribed matching bits -/
noncomputable section
namespace LeanTrominoes.FixedPolyominoSeed.VertexEncoding
open PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder Computability
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance
abbrev MatchingSeed := PeriodicCNF.Seed Nat
abbrev Pin := (Nat × Cell) × Bool

def sourcePeriod : Nat := presentation.finalNormalizationPeriod
attribute [local irreducible] sourcePeriod coarsePeriod tilePeriod

def baseLocation (index : Nat) : Cell :=
  ((List.range FixedPlanarThreeDMSeed.fixedInstance.triples.length).map fun i =>
    presentation.endpointDrawingLocation
      (PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) i) (0,0)).getD index (0,0)

def order (index : Nat) : TrichromaticOrder :=
  ((List.range FixedPlanarThreeDMSeed.fixedInstance.triples.length).map
    (PeriodicThreeDM.SeedNormalization.vertexOrder presentation)).getD index .blueRedGreen

def location (index : Nat) (c : Cell) : Cell :=
  Cell.add (baseLocation index) (PeriodicCNF.Reflection.cell (Cell.scale (sourcePeriod : Int) c))

theorem location_eq (index : Nat) (bound : index < FixedPlanarThreeDMSeed.fixedInstance.triples.length)
    (c : Cell) : location index c = presentation.endpointDrawingLocation
      (PeriodicThreeDM.SeedNormalization.selectedEndpoint (problem := FixedPlanarThreeDMSeed.fixedInstance) index) c := by
  unfold location baseLocation
  simp only [List.getD,List.getElem?_map,List.getElem?_range bound,Option.map_some,Option.getD_some]
  unfold sourcePeriod PeriodicThreeDM.PlanarPresentation.endpointDrawingLocation
  ext <;> simp only [PeriodicThreeDM.reflectedLocation,PeriodicCNF.Reflection.cell,
    Cell.add,Cell.scale,mul_zero,add_zero] <;> ring

theorem order_eq (index : Nat) (bound : index < FixedPlanarThreeDMSeed.fixedInstance.triples.length) :
    order index = PeriodicThreeDM.SeedNormalization.vertexOrder presentation index := by
  simp only [order,List.getD,List.getElem?_map,List.getElem?_range bound,Option.map_some,Option.getD_some]

theorem vertex_type (index : Nat) (bound : index < FixedPlanarThreeDMSeed.fixedInstance.triples.length)
    (c : Cell) : drawing.getAt (location index c) = .trichromaticVertex (order index) := by
  rw [location_eq index bound c,order_eq index bound]
  exact PeriodicThreeDM.SeedNormalization.vertex_type FixedPlanarThreeDMSeed.fixedPresentation
    FixedPlanarThreeDMSeed.fixedInstance_degree FixedPlanarThreeDMSeed.fixedPresentation_collisionFree index bound c

def vertexPins (base : Cell) (seed : MatchingSeed) : CanonicalISelection.VertexSeed :=
  seed.map fun p => ((location p.1.1 (Cell.add base p.1.2),order p.1.1),!p.2)

def placements (base : Cell) (seed : MatchingSeed) : List (Placement Bool) :=
  (CanonicalISelection.seedPlacements (vertexPins base seed)).map fun p =>
    (expandPlacement (p.shift (ShiftedGadgetReadout.inverseOffset (9,3)))).tag false

def Supported (seed : MatchingSeed) : Prop :=
  ∀ p ∈ seed, p.1.1 < FixedPlanarThreeDMSeed.fixedInstance.triples.length

theorem checked (base : Cell) (seed : MatchingSeed) (supported : Supported seed) :
    CanonicalISelection.Checked drawing (vertexPins base seed) := by
  intro p member
  unfold vertexPins at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  exact vertex_type original.1.1 (supported original originalMember) _

theorem baseLocation_primrec : Primrec baseLocation :=
  (Primrec.list_getD (0,0)).comp (Primrec.const _) Primrec.id

theorem order_primrec : Primrec order :=
  (Primrec.list_getD TrichromaticOrder.blueRedGreen).comp (Primrec.const _) Primrec.id

theorem location_primrec : Primrec₂ location :=
  cell_add_primrec.comp (baseLocation_primrec.comp Primrec.fst)
    (PeriodicCNF.Reflection.cell_primrec.comp
      (cell_scale_primrec.comp (Primrec.const (sourcePeriod : Int)) Primrec.snd))

theorem vertexPins_primrec : Primrec₂ vertexPins :=
  Primrec.list_map Primrec.snd
    (Primrec.pair
      (Primrec.pair (location_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (cell_add_primrec.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
        (order_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.not.comp (Primrec.snd.comp Primrec.snd)))

theorem placements_primrec : Primrec₂ placements := by
  have shifted : Primrec (fun p : Placement Unit => p.shift (ShiftedGadgetReadout.inverseOffset (9,3))) :=
    (CanonicalISelection.translatePlacement_primrec.comp
      (Primrec.const (ShiftedGadgetReadout.inverseOffset (9,3))) Primrec.id).of_eq (fun _ => rfl)
  have tagged : Primrec (fun p : Placement Unit => p.tag false) :=
    (Primrec.of_equiv_symm : Primrec PlaneTilingSearch.placementEquiv.symm).comp
      (Primrec.pair (Primrec.const false) (Primrec.pair TrominoAssignment.placement_symmetry_primrec
        TrominoAssignment.placement_offset_primrec))
  exact Primrec.list_map (CanonicalISelection.seedPlacements_primrec.comp vertexPins_primrec)
    ((tagged.comp (expandPlacement_primrec.comp shifted)).comp Primrec.snd)

end LeanTrominoes.FixedPolyominoSeed.VertexEncoding
