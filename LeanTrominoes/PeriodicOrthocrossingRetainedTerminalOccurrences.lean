/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalClassification
import LeanTrominoes.PeriodicOrthocrossingRetainedBendTerminalOccurrences
import LeanTrominoes.PeriodicOrthocrossingRetainedRouteEndpointOccurrences

/-! # Complete finite retained terminal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Under the occurrence-three bound, every enumerated segment terminal
occurs in the retained finite planar-SAT formula. -/
theorem terminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {terminal : SegmentTerminal}
    (terminalMem : terminal ∈ drawingSegmentTerminals
      (PeriodicCNF.incidenceGraph formula)) :
    (Sum.inl (PlanarSATNode.carrier (.terminal terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  rcases drawingSegmentTerminal_bend_or_routeEndpoint_classify
      (PeriodicCNF.incidenceGraph formula) terminalMem with
    terminalBend | terminalEndpoint
  · rcases terminalBend with
      ⟨routeBend, routeBendMem, terminalEq⟩
    exact routeBendTerminal_mem_retainedDrawingPlanarSATFormula
      formula routeBendMem terminalEq
  · rcases terminalEndpoint with
      ⟨endpoint, endpointMem, terminalEq⟩
    subst terminal
    exact routeEndpointTerminal_mem_retainedDrawingPlanarSATFormula
      formula occurrences endpointMem

end LeanTrominoes.PeriodicOrthocrossing
