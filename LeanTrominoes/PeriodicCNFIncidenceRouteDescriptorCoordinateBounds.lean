/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumeration
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCoordinateBounds

/-! # Coordinate bounds for numeric incidence-route descriptors -/

namespace LeanTrominoes.PeriodicCNF

open PeriodicOrthocrossing

/-- Every unshifted coordinate used by a listed numeric route descriptor lies
strictly inside its drawing period. -/
theorem numericRouteDescriptor_coordinateBounds
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ numericRouteDescriptors formula) :
    descriptor.CoordinateBounds := by
  unfold numericRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, taggedMember, rfl⟩
  have edgeMember := tagged_incidence_edge_mem formula taggedMember
  rw [← CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
    formula tagged taggedMember]
  exact routeDescriptor_coordinateBounds wellFormed degree edgeMember

end LeanTrominoes.PeriodicCNF
