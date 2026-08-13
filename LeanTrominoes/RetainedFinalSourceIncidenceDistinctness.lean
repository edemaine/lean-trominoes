/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedSourceIncidenceDistinctness

/-!
# Incidence-key distinctness of the final retained source

This module assembles the componentwise finite distinctness theorem and the
generic preservation lemmas across the retained source's bookkeeping
pipeline.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Finite variable distinctness becomes periodic incidence-key
distinctness after retaining the finite clause positions. -/
theorem
    retainedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedDrawingPositionedPeriodicPlanarSATFormula
      formula).AllIncidenceKeysNodup :=
  positionPeriodicizedPlanarSATFormula_allIncidenceKeysNodup
    formula
    (retainedDrawingPlanarSATFormula formula)
    (retainedDrawingPlanarSATFormula_allAtomsNodup
      formula wellFormed degree isLocal)

/-- Opaque wrapping preserves retained incidence-key distinctness. -/
theorem
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).AllIncidenceKeysNodup := by
  unfold
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
  exact PositionedPeriodicCNF.allIncidenceKeysNodup_rename
    WrappedPeriodicVariable.mk
    wrappedPeriodicVariable_mk_injective
    (retainedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
      formula wellFormed degree isLocal)

/-- Canonical variable gauging preserves retained incidence-key
distinctness. -/
theorem
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).AllIncidenceKeysNodup := by
  unfold
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
  exact
    PositionedPeriodicCNF.allIncidenceKeysNodup_variableGauge
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedDrawingWrappedPeriodicPlanarSATVariableGauge
        formula)
      (retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
        formula wellFormed degree isLocal)

/-- Clause-anchor normalization preserves retained incidence-key
distinctness. -/
theorem
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).AllIncidenceKeysNodup := by
  unfold
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
  exact
    PositionedPeriodicCNF.allIncidenceKeysNodup_anchorNormalize
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula)
      (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
        formula wellFormed degree isLocal)

/-- The final retained positioned periodic planar-SAT source lists no
physical incidence key twice within one clause. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).AllIncidenceKeysNodup := by
  exact
    (congrArg
      (fun source :
          PositionedPeriodicCNF
            (WrappedPeriodicPlanarSATVariable Variable) =>
        source.AllIncidenceKeysNodup)
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_eq
        formula)).mpr
      (@PositionedPeriodicCNF.allIncidenceKeysNodup_deduplicateByLiterals
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula)
        (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
          formula wellFormed degree isLocal))

end PeriodicOrthocrossing
end LeanTrominoes
