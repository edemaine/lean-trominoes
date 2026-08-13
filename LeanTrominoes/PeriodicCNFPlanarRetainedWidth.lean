/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarWidth
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedDegree

/-!
# Width three for the final retained planar SAT formula

Replacing the complete straight-carrier family by selected retained links
does not affect clause arity: both families use the same binary equality
template.  The crossover, bend, routed-clause, and routed-variable families
retain their existing width-three proofs.  This file composes those facts
and transports the result through periodicization and the final gauges.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Every selected retained carrier link uses the binary equality family. -/
theorem retainedDrawingCompleteCarrierFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (retainedDrawingCompleteCarrierFormula graph) :=
  equalityFamily_widthAtMostThree
    (retainedDrawingCompleteCarrierLinks graph)

/-- Retained straight carriers and unchanged bend equalities have width at
most three. -/
theorem retainedDrawingRouteWireFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (retainedDrawingRouteWireFormula graph) := by
  apply
    (formulaWidthAtMost_append_iff 3
      (retainedDrawingCompleteCarrierFormula graph)
      (drawingRouteBendFormula graph)).mpr
  exact
    ⟨retainedDrawingCompleteCarrierFormula_widthAtMostThree graph,
      drawingRouteBendFormula_widthAtMostThree graph⟩

/-- Scoping the retained route variables into the crossover sum preserves
width. -/
theorem retainedScopedDrawingRouteWireFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (retainedScopedDrawingRouteWireFormula graph) :=
  (formulaWidthAtMost_map_iff 3
    (fun node =>
      (Sum.inl node :
        Sum CarrierNode
          (CrossingRecord × CrossoverInternal)))
    id (retainedDrawingRouteWireFormula graph)).mpr
      (retainedDrawingRouteWireFormula_widthAtMostThree graph)

/-- The retained crossover-and-route core has width at most three. -/
theorem retainedDrawingRoutePlanarCoreFormula_widthAtMostThree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    FormulaWidthAtMost 3
      (retainedDrawingRoutePlanarCoreFormula graph) := by
  apply
    (formulaWidthAtMost_append_iff 3
      (drawingCarrierNodeCrossoverFormula graph)
      (retainedScopedDrawingRouteWireFormula graph)).mpr
  exact
    ⟨drawingCarrierNodeCrossoverFormula_widthAtMostThree graph,
      retainedScopedDrawingRouteWireFormula_widthAtMostThree graph⟩

/-- Embedding the retained route core into the full planar-SAT variable type
preserves width. -/
theorem retainedScopedDrawingPlanarSATCore_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    FormulaWidthAtMost 3
      (retainedScopedDrawingPlanarSATCore formula) :=
  (formulaWidthAtMost_map_iff 3
    planarSATCoreVariableMap id
    (retainedDrawingRoutePlanarCoreFormula
      (PeriodicCNF.incidenceGraph formula))).mpr
        (retainedDrawingRoutePlanarCoreFormula_widthAtMostThree
          (PeriodicCNF.incidenceGraph formula))

/-- The complete finite retained routed planar-SAT block preserves width
three. -/
theorem retainedDrawingPlanarSATFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    FormulaWidthAtMost 3
      (retainedDrawingPlanarSATFormula formula) := by
  rw [retainedDrawingPlanarSATFormula,
    formulaWidthAtMost_append_iff,
    formulaWidthAtMost_append_iff]
  exact
    ⟨⟨retainedScopedDrawingPlanarSATCore_widthAtMostThree formula,
        scopedDrawingRoutedClauseFormula_widthAtMostThree
          formula sourceWidth⟩,
      scopedDrawingRoutedVariableFormula_widthAtMostThree formula⟩

/-- Periodicization of the retained finite block preserves its width-three
certificate. -/
theorem retainedDrawingPeriodicPlanarSATFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (retainedDrawingPeriodicPlanarSATFormula
      formula).WidthAtMost 3 := by
  intro periodicClause periodicClauseMember
  rcases List.mem_map.mp periodicClauseMember with
    ⟨embeddedClause, embeddedClauseMember, periodicClauseEq⟩
  subst periodicClause
  have embeddedWidth :=
    retainedDrawingPlanarSATFormula_widthAtMostThree
      formula sourceWidth embeddedClause embeddedClauseMember
  simpa [PeriodicClause.WidthAtMost,
    EmbeddedClause.WidthAtMost,
    periodicizePlanarSATClause] using embeddedWidth

/-- Applying a variable gauge changes literal offsets but not clause
lengths. -/
theorem PeriodicCNF.variableGauge_widthAtMost
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (gauge : Variable → Cell)
    (width : Nat)
    (bounded : source.WidthAtMost width) :
    (source.variableGauge gauge).WidthAtMost width := by
  intro gaugedClause gaugedClauseMember
  rcases List.mem_map.mp gaugedClauseMember with
    ⟨clause, clauseMember, gaugedClauseEq⟩
  subst gaugedClause
  simpa [PeriodicClause.WidthAtMost] using
    bounded clause clauseMember

/-- The final wrapped, gauged, normalized, and deduplicated retained formula
has width at most three. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_widthAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceWidth : formula.WidthAtMost 3) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.WidthAtMost 3 := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase,
    PeriodicCNF.deduplicate_widthAtMost_iff]
  apply PeriodicCNF.anchorNormalize_widthAtMost
  apply PeriodicCNF.variableGauge_widthAtMost
  apply wrapPeriodicPlanarSATFormula_widthAtMost
  exact
    retainedDrawingPeriodicPlanarSATFormula_widthAtMostThree
      formula sourceWidth

end PeriodicOrthocrossing
end LeanTrominoes
