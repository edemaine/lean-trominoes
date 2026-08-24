/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-! # Segment geometry of numeric incidence-route descriptors -/

namespace LeanTrominoes.PeriodicCNF

open PeriodicOrthocrossing

/-- Every segment reconstructed from a listed numeric incidence descriptor is
one of the genuine axis-aligned segments of its semantic graph route. -/
theorem numericRouteDescriptor_segment_axisAligned
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ numericRouteDescriptors formula)
    {segment : GridSegment}
    (segmentMember : segment ∈ gridPolylineSegments descriptor.route) :
    segment.IsAxisAligned := by
  unfold numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨taggedIncidence, taggedMember, descriptorEq⟩
  subst descriptor
  have edgeMember :=
    tagged_incidence_edge_mem formula taggedMember
  have edgeLocal : taggedIncidence.1.edge.span ≤ 1 :=
    isLocal taggedIncidence.1.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have routeOrthogonal :=
    constructedEdgeRoute_orthogonal
      (graph := formula.incidenceGraph)
      (taggedEdge :=
        (taggedIncidence.1.edge, taggedIncidence.2))
      wellFormed degree edgeMember edgeLocal
  rw [← CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
      formula taggedIncidence taggedMember,
    ← constructedEdgeRoute_eq_descriptorRoute] at segmentMember
  exact (orthogonalPolyline_iff_segments _).mp routeOrthogonal
    segment segmentMember

end LeanTrominoes.PeriodicCNF
