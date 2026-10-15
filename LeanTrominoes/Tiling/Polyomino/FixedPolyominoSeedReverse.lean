/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedVertexCorrectness
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedBooleanTransport

/-! # Every completed emitted seed recovers the original Wang input pins -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPolyominoSeed.BooleanTransport
open LeanWang PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
local instance : BEq FinalVariable := instBEqOfDecidableEq
local instance : LawfulBEq FinalVariable := by infer_instance
local instance : BEq PolarityVariable := instBEqOfDecidableEq
local instance : LawfulBEq PolarityVariable := by infer_instance
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedFormula FixedPlanarThreeDMSeed.fixedInstance
attribute [local irreducible] FixedWangAugmentedSeedDecoder.support
attribute [local irreducible] FixedWangAugmentedSeedDecoder.supportedRead
attribute [local irreducible] ShiftedGadgetReadout.assignment

def extra (code : Nat.Partrec.Code) : Nat := VertexEncoding.seedMargin (matchingSeed code)
def base (code : Nat.Partrec.Code) : Cell := AugmentedSoundness.baseline (extra code)

def middleAssignment (code : Nat.Partrec.Code) (ps : Set (Placement Bool))
    (free : PolarityVariable → Cell → Bool) : PolarityVariable → Cell → Bool :=
  fun v c => decode FixedWangAugmentedSeedDecoder.polarityRead (AugmentedSoundness.assignment ps free)
    v (Cell.add (base code) c)

theorem recover_middle (code : Nat.Partrec.Code) (consistent : Consistent (middleSeed code))
    (ps : Set (Placement Bool)) (tiling : IsTiling (pairTiles bumpy largeTile) Set.univ ps)
    (qSeed : referencePlacement ∈ ps)
    (retained : ∀ p ∈ VertexEncoding.placements (base code) (matchingSeed code), p ∈ ps) :
    ∃ free : PolarityVariable → Cell → Bool,
      ∀ pin ∈ middleSeed code, middleAssignment code ps free pin.1.1 pin.1.2 = pin.2 := by
  obtain ⟨bits,pins⟩ := (consistent_iff _).1 consistent
  let free := PeriodicCNF.Translation.assignment (base code) bits
  refine ⟨free,?_⟩
  intro pin member
  by_cases used : pin.1.1 ∈ FixedWangAugmentedSeedDecoder.support
  · unfold middleAssignment
    rw [FixedWangAugmentedSeedDecoder.polarity_decode_supported _ _ used,
      AugmentedSoundness.restrict_assignment]
    have matchingMember : transportPin
        (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead FixedPlanarThreeDMSeed.fixedFormula) pin ∈ matchingSeed code :=
      List.mem_map.mpr ⟨pin,List.mem_filter.mpr ⟨member,by simpa only [decide_eq_true_eq] using used⟩,rfl⟩
    have value := VertexEncoding.matching_pin (matchingSeed code) (matching_supported code) ps tiling qSeed
      retained _ matchingMember
    unfold FixedWangAugmentedSeedDecoder.supportedRead
    rw [decode_compose]
    simpa only [decode,PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead,transportPin,
      ite_true,Cell.add,add_zero,base,extra,FixedPolyominoSeed.presentation] using value
  · unfold middleAssignment
    rw [FixedWangAugmentedSeedDecoder.polarity_decode_unused _ _ used]
    change PeriodicCNF.Translation.assignment (base code) bits pin.1.1 (Cell.add (base code) pin.1.2) = pin.2
    rw [PeriodicCNF.Translation.at_shift]
    exact pins pin member

theorem wangAssignment_eq (code : Nat.Partrec.Code) (ps : Set (Placement Bool))
    (free : PolarityVariable → Cell → Bool) :
    AugmentedSoundness.wangAssignment (extra code) ps free = decode middleRead (middleAssignment code ps free) := by
  have composed : decode FixedWangAugmentedSeedDecoder.read (AugmentedSoundness.assignment ps free) =
      decode middleRead (decode FixedWangAugmentedSeedDecoder.polarityRead (AugmentedSoundness.assignment ps free)) := by
    rw [FixedWangAugmentedSeedDecoder.read,FixedWangAugmentedSeedDecoder.sourceRead,middleRead,
      decode_compose,decode_compose,decode_compose]
  unfold AugmentedSoundness.wangAssignment middleAssignment
  rw [PeriodicCNF.Translation.decode_add,← composed]
  rfl

theorem recover_source (code : Nat.Partrec.Code) (ps : Set (Placement Bool))
    (free : PolarityVariable → Cell → Bool)
    (middlePins : ∀ pin ∈ middleSeed code, middleAssignment code ps free pin.1.1 pin.1.2 = pin.2) :
    ∀ pin ∈ sourceSeed code,
      AugmentedSoundness.wangAssignment (extra code) ps free pin.1.1 pin.1.2 = pin.2 := by
  intro pin member
  rw [wangAssignment_eq]
  exact (pin_correct middleRead _ pin).1
    (middlePins _ (List.mem_map.mpr ⟨pin,member,rfl⟩))

theorem original_seed_origin (code : Nat.Partrec.Code) :
    ∃ corner, (0,corner) ∈ FixedMachineWangSeed.universalReduction code := by
  refine ⟨FixedMachineWangSeed.bottomTile UniversalTM0Machine.machine
    (UniversalTM0Machine.input (UniversalTM0Semantic.input code)) 0,?_⟩
  rw [FixedMachineWangSeed.universalReduction,FixedMachineWangSeed.universalSeedData_eq]
  apply List.mem_map.mpr
  refine ⟨0,?_,rfl⟩
  simp [MachineInputTiles.tailPosition]

theorem reverse (code : Nat.Partrec.Code) (consistent : Consistent (middleSeed code))
    (ps : Set (Placement Bool)) (tiling : IsTiling (pairTiles bumpy largeTile) Set.univ ps)
    (qSeed : referencePlacement ∈ ps)
    (retained : ∀ p ∈ VertexEncoding.placements (base code) (matchingSeed code), p ∈ ps) :
    ¬ (Nat.Partrec.Code.eval code 0).Dom := by
  obtain ⟨free,middlePins⟩ := recover_middle code consistent ps tiling qSeed retained
  have pointed := WangPeriodicCNF.seededQuarter_of_satisfies
    FixedMachineWangSeed.PlaneExtension.universalPlanePalette
    (FixedMachineWangSeed.PlaneExtension.pointedBottomSeed (FixedMachineWangSeed.universalReduction code))
    (AugmentedSoundness.wangAssignment (extra code) ps free)
    (AugmentedSoundness.quarter_satisfies (extra code) ps tiling qSeed free) (by
      have seedEqual : WangPeriodicCNF.pins FixedMachineWangSeed.PlaneExtension.universalPlanePalette
          (WangPeriodicCNF.bottomSeed (FixedMachineWangSeed.PlaneExtension.pointedBottomSeed
            (FixedMachineWangSeed.universalReduction code))) = sourceSeed code := by
        unfold sourceSeed WangPeriodicCNF.fixedSeedReduction FixedMachineWangSeed.PlaneExtension.reduction
        congr 1
        simp only [WangPeriodicCNF.bottomSeed,FixedMachineWangSeed.PlaneExtension.pointedBottomSeed,
          FixedMachineWangSeed.PlaneExtension.seeds,List.map_map,Function.comp_def]
      rw [seedEqual]
      exact recover_source code ps free middlePins)
  obtain ⟨corner,atOrigin⟩ := original_seed_origin code
  exact (FixedMachineWangSeed.universalReduction_correct code).1
    (FixedMachineWangSeed.PlaneExtension.quarter_of_seeded_quarter atOrigin pointed)

end LeanTrominoes.FixedPolyominoSeed.BooleanTransport
