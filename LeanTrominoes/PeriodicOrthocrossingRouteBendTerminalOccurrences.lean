/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarBends
import LeanTrominoes.PlanarThreeSATEqualityEndpointOccurrences

/-! # Terminal occurrences in route-bend equality families -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every enumerated bend contributes its equality link to the global bend
link list. -/
theorem RouteBend.equalityLink_mem_drawingRouteBendLinks
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph) :
    routeBend.equalityLink graph ∈ drawingRouteBendLinks graph := by
  unfold drawingRouteBendLinks
  apply List.mem_map.mpr
  exact ⟨routeBend, by simpa using routeBendMem, rfl⟩

/-- Both segment terminals adjacent to an enumerated bend occur in the bend
equality formula. -/
theorem routeBendTerminal_mem_drawingRouteBendFormula
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends graph)
    {terminal : SegmentTerminal}
    (terminalEq : terminal = routeBend.incomingTerminal ∨
      terminal = routeBend.outgoingTerminal) :
    CarrierNode.terminal terminal ∈ embeddedVariableOccurrences
      (drawingRouteBendFormula graph) := by
  have linkMem :=
    RouteBend.equalityLink_mem_drawingRouteBendLinks
      graph routeBendMem
  rcases terminalEq with rfl | rfl
  · exact
      EqualityLink.first_mem_embeddedVariableOccurrences_equalityFamily
        linkMem
  · exact
      EqualityLink.second_mem_embeddedVariableOccurrences_equalityFamily
        linkMem

end LeanTrominoes.PeriodicOrthocrossing
