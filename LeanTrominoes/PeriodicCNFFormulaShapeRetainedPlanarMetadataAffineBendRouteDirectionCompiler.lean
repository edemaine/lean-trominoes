/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for complete retained-bend route direction words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

/-- The finite affine predicate table selects every complete route-delimited
bend word in polynomial time. -/
noncomputable def affineBaseBendRouteDirectionBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendRouteDirectionBlock :=
  predicateListBlocksComputableInPolyTime bendDescriptorPredicates
    (allRouteShapes.flatMap RouteShape.bendRouteDirectionBlocks)

/-- Mapping the bend-word selector over the tagged descriptor-pair stream is
polynomial time. -/
noncomputable def affineBaseBendRouteDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      affineBaseBendRouteDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBaseBendRouteDirectionBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
