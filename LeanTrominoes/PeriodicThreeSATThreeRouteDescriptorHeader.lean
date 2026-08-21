/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorFacts
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount

/-! # Constant route-descriptor fields after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every route of the occurrence-split formula uses the same exact drawing
vertex count: one vertex per source clause and two per source literal. -/
@[simp] theorem numericRouteDescriptor_formula_vertexCount
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (edgeIndex : Nat) :
    (incidence.numericRouteDescriptor (formula source) edgeIndex).vertexCount =
      source.clauses.length +
        2 * PeriodicCNF.presentationLiteralCount source := by
  simp [CNFIncidence.numericRouteDescriptor]
  omega

/-- The occurrence-split formula has three route descriptors per source
literal: one copied incidence and two implication-cycle incidences. -/
@[simp] theorem numericRouteDescriptor_formula_edgeCount
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (edgeIndex : Nat) :
    (incidence.numericRouteDescriptor (formula source) edgeIndex).edgeCount =
      3 * PeriodicCNF.presentationLiteralCount source := by
  change (PeriodicCNF.incidencesWithMetadata (formula source)).length = _
  calc
    _ = (formula source).incidenceGraph.edges.length :=
      (PeriodicCNF.incidenceGraph_edges_length_eq_metadata _).symm
    _ = PeriodicCNF.presentationLiteralCount (formula source) :=
      PeriodicCNF.incidenceGraph_edges_length _
    _ = 3 * PeriodicCNF.presentationLiteralCount source :=
      formula_presentationLiteralCount source

/-- Clause vertices follow all occurrence-variable vertices, whose exact count
is the number of source literal occurrences. -/
@[simp] theorem numericRouteDescriptor_formula_sourceVertexIndex
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (edgeIndex : Nat) :
    (incidence.numericRouteDescriptor
      (formula source) edgeIndex).sourceVertexIndex =
        PeriodicCNF.presentationLiteralCount source +
          incidence.clauseIndex := by
  simp [CNFIncidence.numericRouteDescriptor]

end PeriodicThreeSATThree
end LeanTrominoes
