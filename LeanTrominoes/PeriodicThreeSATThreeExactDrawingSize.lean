/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount
import LeanTrominoes.PeriodicCNFIncidenceGraphSize

/-! # Exact orthocrossing scale after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

@[simp] theorem incidenceGraph_vertices_length_formula
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.incidenceGraph (formula source)).vertices.length =
      source.clauses.length +
        2 * PeriodicCNF.presentationLiteralCount source := by
  simp only [PeriodicCNF.incidenceGraph, List.length_append,
    PeriodicCNF.incidenceVariableVertices,
    PeriodicCNF.incidenceClauseVertices, List.length_map,
    List.length_range, formula_variableOccurrences_dedup_length,
    formula_clauses_length]
  omega

/-- After occurrence splitting, the generic orthocrossing grid has exact
scale `16 * (clauses + 5 * literals + 1)`. -/
@[simp] theorem drawingGridSize_incidenceGraph_formula
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    PeriodicOrthocrossing.drawingGridSize
        (PeriodicCNF.incidenceGraph (formula source)) =
      16 * (source.clauses.length +
        5 * PeriodicCNF.presentationLiteralCount source + 1) := by
  unfold PeriodicOrthocrossing.drawingGridSize
  rw [incidenceGraph_vertices_length_formula,
    PeriodicCNF.incidenceGraph_edges_length,
    formula_presentationLiteralCount]
  omega

end PeriodicThreeSATThree
end LeanTrominoes
