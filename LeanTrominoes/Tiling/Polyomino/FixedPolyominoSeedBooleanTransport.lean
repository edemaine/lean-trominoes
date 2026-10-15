/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedVertexEncoding

/-! # Transporting a universal-machine input to supported matching pins -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPolyominoSeed.BooleanTransport
open LeanWang PeriodicCNF.SignedDecoder PeriodicOrthocrossing
abbrev PolarityVariable := FixedPlanarThreeDMSeed.Variable
abbrev FinalVariable := FixedPlanarThreeDMSeed.FinalVariable
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
local instance : BEq FinalVariable := instBEqOfDecidableEq
local instance : LawfulBEq FinalVariable := by infer_instance
local instance : BEq PolarityVariable := instBEqOfDecidableEq
local instance : LawfulBEq PolarityVariable := by infer_instance
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedFormula FixedPlanarThreeDMSeed.fixedInstance

def sourceSeed (code : Nat.Partrec.Code) : PeriodicCNF.Seed WangTile :=
  WangPeriodicCNF.fixedSeedReduction (FixedMachineWangSeed.PlaneExtension.reduction code)

def middleRead : Read WangTile PolarityVariable :=
  compose FixedWangNormalizedSeedDecoder.threeRead (retainedPolaritySeedRead FixedThreeSATThreeSeed.fixedFormula)

def middleSeed (code : Nat.Partrec.Code) : PeriodicCNF.Seed PolarityVariable :=
  transportSeed middleRead (sourceSeed code)

def matchingSeed (code : Nat.Partrec.Code) : PeriodicCNF.Seed Nat :=
  transportSeed (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead FixedPlanarThreeDMSeed.fixedFormula)
    (supportedPart FixedWangAugmentedSeedDecoder.support (middleSeed code))

theorem middleFactor : LogicalFactor WangPeriodicCNF.fixedFormula.Satisfies
    (PeriodicOneInThree.Satisfies FixedPlanarThreeDMSeed.fixedFormula) middleRead Set.univ := by
  unfold FixedPlanarThreeDMSeed.fixedFormula
  exact FixedWangNormalizedSeedDecoder.threeFactor.logical.compose
    (retainedPolaritySeedFactor FixedThreeSATThreeSeed.fixedFormula
      FixedThreeSATThreeSeed.fixedFormula_isLocal FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree
      FixedPlanarThreeDMSeed.source_occurrences FixedThreeSATThreeSeed.fixedFormula_clausesNonempty)
    (fun _ _ => Set.mem_univ _)

theorem source_completed (code : Nat.Partrec.Code) (nonhalting : ¬ (Nat.Partrec.Code.eval code 0).Dom) :
    WangPeriodicCNF.fixedFormula.Seeded (sourceSeed code) :=
  (WangPeriodicCNF.seeded_iff_completable _ _).2
    ((FixedMachineWangSeed.PlaneExtension.reduction_correct code).2 nonhalting)

theorem middle_completed (code : Nat.Partrec.Code) (nonhalting : ¬ (Nat.Partrec.Code.eval code 0).Dom) :
    Prescribed (PeriodicOneInThree.Satisfies FixedPlanarThreeDMSeed.fixedFormula) (middleSeed code) :=
  (middleFactor.seeded_iff (sourceSeed code) (fun _ _ => Set.mem_univ _)).1 (source_completed code nonhalting)

theorem matching_completed (code : Nat.Partrec.Code)
    (completed : Prescribed (PeriodicOneInThree.Satisfies FixedPlanarThreeDMSeed.fixedFormula) (middleSeed code)) :
    Prescribed FixedPlanarThreeDMSeed.fixedInstance.Satisfies (matchingSeed code) := by
  unfold FixedPlanarThreeDMSeed.fixedInstance matchingSeed
  apply (PeriodicPlanarOneInThreeToThreeDM.encodedSeedFactor FixedPlanarThreeDMSeed.fixedFormula
    FixedPlanarThreeDMSeed.fixedFormula_occurrences FixedPlanarThreeDMSeed.fixedFormula_arity).seeded_iff
      (supportedPart FixedWangAugmentedSeedDecoder.support (middleSeed code))
      (fun pin member => of_decide_eq_true (List.mem_filter.mp member).2) |>.1
  obtain ⟨a,ha,pins⟩ := completed
  exact ⟨a,ha,fun pin member => pins pin (List.mem_filter.mp member).1⟩

theorem matching_supported (code : Nat.Partrec.Code) : VertexEncoding.Supported (matchingSeed code) := by
  intro pin member
  unfold matchingSeed transportSeed at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  have used : original.1.1 ∈ PeriodicPlanarOneInThreeToThreeDM.occurringVariables
      FixedPlanarThreeDMSeed.fixedFormula := of_decide_eq_true (List.mem_filter.mp originalMember).2
  have bound := List.idxOf_lt_length_iff.mpr
    (PeriodicPlanarOneInThreeToThreeDM.seedTriple_mem FixedPlanarThreeDMSeed.fixedFormula original.1.1 used)
  unfold FixedPlanarThreeDMSeed.fixedInstance PeriodicPlanarOneInThreeToThreeDM.encodedProblem
  simpa only [transportPin,PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,List.length_map] using bound

theorem sourceSeed_computable : Computable sourceSeed :=
  WangPeriodicCNF.fixedSeedReduction_primrec.to_comp.comp FixedMachineWangSeed.PlaneExtension.reduction_computable

theorem middleRead_primrec : Primrec middleRead :=
  compose_primrec
    (compose_primrec PeriodicThreeCNF.seedRead_primrec (PeriodicThreeSATThree.seedRead_primrec _))
    (retainedPolaritySeedRead_primrec _)

theorem middleSeed_computable : Computable middleSeed :=
  (transportSeed_primrec middleRead_primrec).to_comp.comp sourceSeed_computable

theorem matchingSeed_computable : Computable matchingSeed :=
  (transportSeed_primrec (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead_primrec _)).to_comp.comp
    ((supportedPart_primrec FixedWangAugmentedSeedDecoder.support).to_comp.comp middleSeed_computable)

end LeanTrominoes.FixedPolyominoSeed.BooleanTransport
