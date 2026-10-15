/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedForward
import LeanTrominoes.Tiling.Polyomino.FixedPolyominoSeedBooleanTransport

/-! # A computable machine-input seed for the two fixed polyominoes -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPolyominoSeed
open LeanWang PlusRefinement Gadget KeyedPeriodicComplement PeriodicCNF.SignedDecoder PeriodicOrthocrossing
abbrev PolarityVariable := FixedPlanarThreeDMSeed.Variable
abbrev FinalVariable := FixedPlanarThreeDMSeed.FinalVariable
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
attribute [local irreducible] VertexEncoding.placements VertexEncoding.vertexPins
attribute [local irreducible] CanonicalISelection.seedPlacements CanonicalISelection.trichromaticPattern
attribute [local irreducible] FixedPlanarThreeDMSeed.fixedFormula FixedPlanarThreeDMSeed.fixedInstance
attribute [local irreducible] BooleanTransport.matchingSeed BooleanTransport.middleSeed BooleanTransport.sourceSeed
attribute [local irreducible] VertexEncoding.seedMargin AugmentedSoundness.baseline

def impossibleSeed : List (Placement Bool) :=
  [⟨false,.identity,(0,0)⟩,⟨false,.identity,(1,0)⟩]

theorem impossibleSeed_not_completed : ¬ Problem impossibleSeed := by
  rintro completed
  obtain ⟨ps,tiling,retained⟩ := (VertexEncoding.problem_iff _).1 completed
  have first := retained ⟨false,.identity,(0,0)⟩ (by simp [impossibleSeed])
  have second := retained ⟨false,.identity,(1,0)⟩ (by simp [impossibleSeed])
  have disjoint := tiling.disjoint_cells first second (by decide)
  exact (Finset.disjoint_left.mp disjoint) (a := (1,0)) (by decide) (by decide)

def reduction (code : Nat.Partrec.Code) : List (Placement Bool) :=
  if Consistent (BooleanTransport.middleSeed code) then
    referencePlacement :: VertexEncoding.placements
      (AugmentedSoundness.baseline (VertexEncoding.seedMargin (BooleanTransport.matchingSeed code)))
      (BooleanTransport.matchingSeed code)
  else impossibleSeed

theorem reduction_computable : Computable reduction := by
  have arguments : Computable (fun code : Nat.Partrec.Code =>
      (AugmentedSoundness.baseline (VertexEncoding.seedMargin (BooleanTransport.matchingSeed code)),
        BooleanTransport.matchingSeed code)) :=
    (Primrec.pair VertexEncoding.baseline_primrec Primrec.id).to_comp.comp
      BooleanTransport.matchingSeed_computable
  have emitted : Computable (fun code : Nat.Partrec.Code =>
      VertexEncoding.placements
        (AugmentedSoundness.baseline (VertexEncoding.seedMargin (BooleanTransport.matchingSeed code)))
        (BooleanTransport.matchingSeed code)) := VertexEncoding.placements_primrec.to_comp.comp
          (Computable.fst.comp arguments) (Computable.snd.comp arguments)
  have yes : Computable (fun code : Nat.Partrec.Code =>
      referencePlacement :: VertexEncoding.placements
        (AugmentedSoundness.baseline (VertexEncoding.seedMargin (BooleanTransport.matchingSeed code)))
        (BooleanTransport.matchingSeed code)) :=
    (Primrec.list_cons.comp (Primrec.const referencePlacement) Primrec.id).to_comp.comp emitted
  exact (Computable.cond
    (consistent_primrec.computablePred.decide.comp BooleanTransport.middleSeed_computable)
    yes (Computable.const impossibleSeed)).of_eq (fun _ => by
      simp only [Bool.cond_decide]; rfl)

theorem reduction_forward (code : Nat.Partrec.Code) (nonhalting : ¬ (Nat.Partrec.Code.eval code 0).Dom) :
    Problem (reduction code) := by
  have middle := BooleanTransport.middle_completed code nonhalting
  have consistent : Consistent (BooleanTransport.middleSeed code) :=
    (consistent_iff _).2 ⟨middle.choose,middle.choose_spec.2⟩
  rw [reduction,if_pos consistent]
  exact VertexEncoding.forward _ _ (BooleanTransport.matching_supported code)
    (BooleanTransport.matching_completed code middle)

end LeanTrominoes.FixedPolyominoSeed
