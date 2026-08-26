/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBaseBendScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Compiler for untranslated retained-bend descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing RouteDescriptorPairFieldTags

/-- The finite predicate table computes one untranslated bend block. -/
noncomputable def affineBaseBendDescriptorBlockComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBaseBendDescriptorBlock :=
  predicateListBlocksComputableInPolyTime
    bendDescriptorPredicates bendDescriptorBlocks

/-- Mapping the untranslated bend selector over every tagged descriptor pair
is polynomial time. -/
noncomputable def affineBaseBendDescriptorStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineBaseBendDescriptorStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    affineBaseBendDescriptorBlockComputableInPolyTime isPairEnd

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes

end
