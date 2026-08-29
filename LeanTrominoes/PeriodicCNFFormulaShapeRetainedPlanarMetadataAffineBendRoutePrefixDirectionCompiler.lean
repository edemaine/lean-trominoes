/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for retained-bend route source prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

/-- The finite affine predicate table selects every route-delimited bend
source prefix in polynomial time. -/
noncomputable def affineBaseBendRoutePrefixDirectionBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBaseBendRoutePrefixDirectionBlock :=
  predicateListBlocksComputableInPolyTime bendDescriptorPredicates
    (allRouteShapes.flatMap RouteShape.bendRoutePrefixDirectionBlocks)

/-- Mapping the bend-prefix selector over the tagged descriptor-pair stream
is polynomial-time computable. -/
noncomputable def affineBaseBendRoutePrefixDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBaseBendRoutePrefixDirectionStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBaseBendRoutePrefixDirectionBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
