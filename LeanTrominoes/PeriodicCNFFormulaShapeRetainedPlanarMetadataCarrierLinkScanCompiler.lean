/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkScanData

/-! # Polynomial-time retained carrier-link block expansion -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open Computability Turing

/-- The fixed two-token expansion of an already ordered carrier-link bit
stream is polynomial-time computable. -/
noncomputable def carrierLinkDescriptorScanComputableInPolyTime :
    TM2ComputableInPolyTime id id carrierLinkDescriptorScan :=
  FiniteBlockTransducer.computableInPolyTime fun bits : Bool × Bool =>
    compiledCarrierLinkDescriptorBlock bits.1 bits.2

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF

end
