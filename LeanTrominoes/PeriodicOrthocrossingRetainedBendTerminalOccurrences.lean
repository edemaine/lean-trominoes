/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedOccurrences
import LeanTrominoes.PeriodicOrthocrossingRouteBendTerminalOccurrences

/-! # Retaining finite route-bend terminal occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Both terminals adjacent to every enumerated route bend occur in the
complete retained finite planar-SAT formula. -/
theorem routeBendTerminal_mem_retainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {routeBend : RouteBend}
    (routeBendMem : routeBend ∈ drawingRouteBends
      (PeriodicCNF.incidenceGraph formula))
    {terminal : SegmentTerminal}
    (terminalEq : terminal = routeBend.incomingTerminal ∨
      terminal = routeBend.outgoingTerminal) :
    (Sum.inl (PlanarSATNode.carrier (.terminal terminal)) :
        PlanarSATVariable Variable) ∈
      embeddedVariableOccurrences
        (retainedDrawingPlanarSATFormula formula) := by
  exact retainedDrawingPlanarSATFormula_terminal_bend_occurrence
    formula terminal
    (routeBendTerminal_mem_drawingRouteBendFormula
      (PeriodicCNF.incidenceGraph formula) routeBendMem terminalEq)

end LeanTrominoes.PeriodicOrthocrossing
