/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableRouteDirections
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableDescriptorTemplateData

/-! # Finite retained routed-variable descriptor templates -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Whether the second endpoint of a normalized routed-variable arm is in
the next horizontal period slice. -/
def routedVariableLinkNextSlice
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink (PlanarSATNode Variable)) : Bool :=
  decide
    ((PeriodicEquality.normalizeLink
      (externalWrappedVariableNormalization source) link).relativeOffset =
        ((1, 0) : Cell))

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
