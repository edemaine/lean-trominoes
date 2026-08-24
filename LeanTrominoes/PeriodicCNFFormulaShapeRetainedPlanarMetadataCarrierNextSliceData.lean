/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierVariableNormalizationData
import LeanTrominoes.PeriodicEqualityNormalization

/-! # Retained carrier next-slice data -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Whether the second endpoint of a canonically normalized carrier link is
in the next horizontal period slice. -/
def carrierLinkNextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) : Bool :=
  decide
    ((PeriodicEquality.normalizeLink
      (carrierWrappedVariableNormalization source) link).relativeOffset =
        ((1, 0) : Cell))

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
