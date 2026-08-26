/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkScanCompiler
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRankOrderedDescriptorData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairCompiler

/-! # Compiler for rank-ordered retained carrier-link descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Computability Turing
open PeriodicOrthocrossing

/-- The complete retained carrier-link descriptor scan is polynomial-time
computable from numeric route descriptors. -/
noncomputable def rankOrderedCarrierLinkDescriptorScanComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
      rankOrderedCarrierLinkDescriptorScan := by
  change TM2ComputableInPolyTime CarrierRankOrderedPairs.InputEncoding id
    (fun descriptors => carrierLinkDescriptorScan
      (CarrierRankOrderedPairs.retainedPairBits descriptors))
  exact TM2CompositionMachine.computableInPolyTime
    CarrierRankOrderedPairs.retainedPairBitsComputableInPolyTime
    carrierLinkDescriptorScanComputableInPolyTime

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

end
