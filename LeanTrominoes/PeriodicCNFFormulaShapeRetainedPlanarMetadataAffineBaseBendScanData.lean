/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData

/-! # Untranslated affine retained-bend descriptor scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Pair-major bend scan with the neighboring-translation repetition removed.
Periodic normalization identifies those nine physical copies. -/
def affineBaseBendDescriptorStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendDescriptorBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
