/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingPlanarBends

/-! # Numeric enumeration of incidence-route bends -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The route-major numeric descriptor expansion reconstructs the semantic
drawing's complete neighboring bend enumeration exactly. -/
theorem incidenceGraph_drawingRouteBends_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    drawingRouteBends formula.incidenceGraph =
      (numericRouteDescriptors formula).flatMap fun descriptor =>
        neighborTranslations.flatMap fun translate =>
          routeBends descriptor.edgeIndex translate descriptor.route := by
  unfold drawingRouteBends PeriodicOrthocrossing.drawing
  rw [incidenceGraph_constructedEdgeRoutes_eq_numeric]
  unfold numericEdgeRoutes
  rw [List.zipIdx_map, List.flatMap_map]
  conv_rhs =>
    rw [← List.zipIdx_map_fst
      (l := numericRouteDescriptors formula) (i := 0)]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro taggedDescriptor taggedMember
  have indexEq :=
    numericRouteDescriptors_selfIndexed formula
      taggedDescriptor taggedMember
  simp [indexEq]

end PeriodicCNF
end LeanTrominoes
