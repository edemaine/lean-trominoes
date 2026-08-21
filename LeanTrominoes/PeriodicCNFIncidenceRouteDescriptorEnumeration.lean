/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSemantics

/-! # Correctness of numeric CNF route and segment enumerations -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- Semantic graph descriptors are exactly the metadata-driven numeric
descriptor stream. -/
theorem incidenceGraph_routeDescriptors_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicOrthocrossing.routeDescriptors formula.incidenceGraph =
      numericRouteDescriptors formula := by
  unfold PeriodicOrthocrossing.routeDescriptors numericRouteDescriptors
  rw [← incidencesWithMetadata_edges, List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  intro tagged taggedMember
  exact CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
    formula tagged taggedMember

/-- Reconstructing each numeric descriptor gives exactly the semantic
constructed edge-route list. -/
theorem incidenceGraph_constructedEdgeRoutes_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PeriodicOrthocrossing.constructedEdgeRoutes formula.incidenceGraph =
      numericEdgeRoutes formula := by
  rw [PeriodicOrthocrossing.constructedEdgeRoutes_eq_descriptorRoutes,
    incidenceGraph_routeDescriptors_eq_numeric]
  rfl

/-- The compact numeric enumeration reconstructs the canonical drawing's
complete indexed-segment stream exactly. -/
theorem incidenceGraph_indexedSegments_eq_numeric
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (PeriodicOrthocrossing.drawing formula.incidenceGraph).indexedSegments =
      numericIndexedSegments formula := by
  unfold PeriodicGridDrawing.indexedSegments
    PeriodicOrthocrossing.drawing numericIndexedSegments
  rw [incidenceGraph_constructedEdgeRoutes_eq_numeric]

end PeriodicCNF
end LeanTrominoes
