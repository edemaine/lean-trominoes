/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteEndpointMetadata
import LeanTrominoes.PeriodicOrthocrossingRetainedSourceTerminalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedTargetTerminalOccurrences

/-! # Retaining finite route-endpoint occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Under the occurrence-three bound, every enumerated external route
endpoint occurs in the retained finite planar-SAT formula. -/
theorem routeEndpointTerminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {endpoint : RouteEndpoint (CNFVertex Variable)}
    (endpointMem : endpoint ∈ drawingRouteEndpoints
      (PeriodicCNF.incidenceGraph formula)) :
    (Sum.inl (PlanarSATNode.carrier (.terminal endpoint.terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  rcases drawingRouteEndpoint_exists_metadataEndpoint
      formula endpointMem with
    ⟨routeEndpoint, occurrenceMem, routeEndpointMem, endpointEq⟩
  subst endpoint
  rcases routeEndpoint.terminal_eq_source_or_target_metadata
      formula routeEndpointMem with
    ⟨_, terminalEq⟩ | ⟨_, terminalEq⟩
  · rw [terminalEq]
    exact sourceTerminal_mem_retainedDrawingPlanarSATFormula
      formula occurrenceMem
  · rw [terminalEq]
    exact targetTerminal_mem_retainedDrawingPlanarSATFormula
      formula occurrences occurrenceMem

end LeanTrominoes.PeriodicOrthocrossing
