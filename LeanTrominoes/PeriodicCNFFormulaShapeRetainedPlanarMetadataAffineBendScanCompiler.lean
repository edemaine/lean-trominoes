/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiler for the finite affine retained-bend descriptor scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

abbrev BendDescriptorToken :=
  PeriodicCNF.FormulaShapeDirectionOrdering.Token

/-- Repeating one output word over the fixed nine neighboring translations is
polynomial time.  A balanced append tree keeps the machine term compact. -/
noncomputable def
    repeatNeighborBendDescriptorBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      repeatNeighborBendDescriptorBlock := by
  let one :
      TM2ComputableInPolyTime id id
        (fun block : List BendDescriptorToken => block) :=
    PeriodicCNF.AffineEmitterPipeline.identityComputableInPolyTime
  let two :
      TM2ComputableInPolyTime id id
        (fun block : List BendDescriptorToken => block ++ block) :=
    TM2ListAppend.nativeComputableInPolyTime one one
  let four :
      TM2ComputableInPolyTime id id
        (fun block : List BendDescriptorToken =>
          (block ++ block) ++ (block ++ block)) :=
    TM2ListAppend.nativeComputableInPolyTime two two
  let eight :
      TM2ComputableInPolyTime id id
        (fun block : List BendDescriptorToken =>
          ((block ++ block) ++ (block ++ block)) ++
            ((block ++ block) ++ (block ++ block))) :=
    TM2ListAppend.nativeComputableInPolyTime four four
  let nine :
      TM2ComputableInPolyTime id id
        (fun block : List BendDescriptorToken =>
          (((block ++ block) ++ (block ++ block)) ++
              ((block ++ block) ++ (block ++ block))) ++ block) :=
    TM2ListAppend.nativeComputableInPolyTime eight one
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (fun block : List BendDescriptorToken =>
      (((block ++ block) ++ (block ++ block)) ++
          ((block ++ block) ++ (block ++ block))) ++ block)
    repeatNeighborBendDescriptorBlock
    (fun block => by
      simp [repeatNeighborBendDescriptorBlock,
        neighborTranslations, neighborCoordinates])
    nine

/-- The complete selected and ninefold-repeated block for one tagged pair is
polynomial time. -/
noncomputable def affineBendDescriptorBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBendDescriptorBlock := by
  let selected :=
    predicateListBlocksComputableInPolyTime
      bendDescriptorPredicates bendDescriptorBlocks
  let repeated :=
    repeatNeighborBendDescriptorBlockComputableInPolyTime
  let composed :=
    TM2CompositionMachine.computableInPolyTime selected repeated
  exact composed

/-- Mapping the affine bend selector independently over a complete tagged
descriptor-pair stream is polynomial time. -/
noncomputable def affineBendDescriptorStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBendDescriptorStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBendDescriptorBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
