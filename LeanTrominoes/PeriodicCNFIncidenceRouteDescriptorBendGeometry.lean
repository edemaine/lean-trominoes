/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration
import LeanTrominoes.PeriodicOrthocrossingBendCornerDrawingFamily

/-! # Corner geometry of numeric incidence-route bends -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

/-- Every bend reconstructed from a listed numeric incidence descriptor has
the genuine nonreversing corner geometry of its semantic graph route. -/
theorem numericRouteDescriptor_routeBend_cornerGeometry
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ numericRouteDescriptors formula)
    (translate : Cell)
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        routeBends descriptor.edgeIndex translate descriptor.route) :
    routeBend.CornerGeometry := by
  unfold numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨taggedIncidence, taggedMember, descriptorEq⟩
  subst descriptor
  have edgeMember :=
    tagged_incidence_edge_mem formula taggedMember
  have edgeLocal : taggedIncidence.1.edge.span ≤ 1 :=
    isLocal taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  apply routeBends_cornerGeometry
    taggedIncidence.2 translate
    (points :=
      (taggedIncidence.1.numericRouteDescriptor
        formula taggedIncidence.2).route)
  · rw [← CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
      formula taggedIncidence taggedMember,
      ← constructedEdgeRoute_eq_descriptorRoute]
    exact constructedEdgeRoute_orthogonal
      (graph := formula.incidenceGraph)
      (taggedEdge :=
        (taggedIncidence.1.edge, taggedIncidence.2))
      wellFormed degree edgeMember edgeLocal
  · rw [← CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
      formula taggedIncidence taggedMember,
      ← constructedEdgeRoute_eq_descriptorRoute]
    exact constructedEdgeRoute_hasNoImmediateReversal
      (graph := formula.incidenceGraph)
      (taggedEdge :=
        (taggedIncidence.1.edge, taggedIncidence.2))
      wellFormed degree edgeMember edgeLocal
  · exact routeBendMember

end PeriodicCNF
end LeanTrominoes
