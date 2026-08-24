/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentScanData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamCompiler

/-! # Compiler for the affine base carrier-segment bit scan -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open Computability Turing

/-- The fixed affine scan producing one axis candidate for every selected
neighboring base segment occurrence is polynomial-time computable. -/
noncomputable def affineCarrierSegmentBitStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id affineCarrierSegmentBitStream :=
  predicateListBlockStreamComputableInPolyTime
    carrierSegmentPredicates carrierSegmentBitBlocks

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

end
