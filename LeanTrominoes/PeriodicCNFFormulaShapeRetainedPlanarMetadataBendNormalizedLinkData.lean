/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierNormalizationInjectivity
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicOrthocrossingPlanarBends

/-! # Canonical normalized retained-bend links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- One routed bend's equality link after the wrapped periodic normalization
used by the retained planar formula. -/
def wrappedNormalizedRouteBendLink
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (routeBend : RouteBend) :
    PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable) :=
  PeriodicEquality.normalizeLink
    (carrierWrappedVariableNormalization source)
    (routeBend.equalityLink source.incidenceGraph)

/-- Normalized bend links of one numeric route occurrence. -/
def translatedRouteBendNormalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (descriptor : RouteDescriptor)
    (translate : Cell) :
    List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)) :=
  (routeBends descriptor.edgeIndex translate descriptor.route).map
    (wrappedNormalizedRouteBendLink source)

/-- One untranslated normalized bend-link block per numeric incidence route. -/
def baseBendNormalizedLinks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (PeriodicEquality.NormalizedLink
      (WrappedPeriodicPlanarSATVariable Variable)) :=
  (numericRouteDescriptors source).flatMap fun descriptor =>
    translatedRouteBendNormalizedLinks source descriptor (0, 0)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
