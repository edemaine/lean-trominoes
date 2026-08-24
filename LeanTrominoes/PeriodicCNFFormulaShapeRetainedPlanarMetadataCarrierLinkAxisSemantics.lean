/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinkAxisSemantics
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration

/-! # Descriptor-derived axes of retained carrier links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The descriptor-derived unary axis value of a retained carrier key is the
zero-or-one encoding of the physical axis of every representative link in
that key's block. -/
theorem retainedRepresentativeCarrierLink_axisValue
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ retainedRepresentativeCarrierLinksAt
        formula.incidenceGraph key) :
    RouteDescriptorCarrierKeyAxisDatum.value
        (numericRouteDescriptors formula) (some key) =
      FixedAxisUnaryFields.value true link.first.isHorizontal := by
  apply retainedRepresentativeCarrierLink_axisValue_of_indexedSegments
    formula.incidenceGraph (numericRouteDescriptors formula)
    _ key linkMember
  rw [incidenceGraph_indexedSegments_eq_numeric]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
