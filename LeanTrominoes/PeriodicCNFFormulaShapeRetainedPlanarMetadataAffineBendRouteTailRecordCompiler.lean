/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFAffineEmitterPipeline
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteTailRecordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Compiler for affine retained-bend Figure 9 tail records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

noncomputable def
    repeatNeighborBendRouteTailRecordBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      repeatNeighborBendRouteTailRecordBlock := by
  let one :
      TM2ComputableInPolyTime id id
        (fun block : List BendRouteTailRecordToken => block) :=
    PeriodicCNF.AffineEmitterPipeline.identityComputableInPolyTime
  let two := TM2ListAppend.nativeComputableInPolyTime one one
  let four := TM2ListAppend.nativeComputableInPolyTime two two
  let eight := TM2ListAppend.nativeComputableInPolyTime four four
  let nine := TM2ListAppend.nativeComputableInPolyTime eight one
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (fun block : List BendRouteTailRecordToken =>
      (((block ++ block) ++ (block ++ block)) ++
          ((block ++ block) ++ (block ++ block))) ++ block)
    repeatNeighborBendRouteTailRecordBlock
    (fun block => by
      simp [repeatNeighborBendRouteTailRecordBlock,
        neighborTranslations, neighborCoordinates])
    nine

noncomputable def affineBendRouteTailRecordBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBendRouteTailRecordBlock := by
  change TM2ComputableInPolyTime id id (fun tokens =>
    repeatNeighborBendRouteTailRecordBlock
      (predicateListBlocks bendDescriptorPredicates
        (allRouteShapes.flatMap RouteShape.bendRouteTailRecordBlocks)
        tokens))
  let selected :=
    predicateListBlocksComputableInPolyTime
      bendDescriptorPredicates
      (allRouteShapes.flatMap RouteShape.bendRouteTailRecordBlocks)
  exact TM2CompositionMachine.computableInPolyTime selected
    repeatNeighborBendRouteTailRecordBlockComputableInPolyTime

noncomputable def affineBaseBendRouteTailRecordStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBaseBendRouteTailRecordStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    (predicateListBlocksComputableInPolyTime
      bendDescriptorPredicates
      (allRouteShapes.flatMap RouteShape.bendRouteTailRecordBlocks))
    isPairEnd

noncomputable def affineBendRouteTailRecordStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBendRouteTailRecordStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBendRouteTailRecordBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
