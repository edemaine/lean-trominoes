/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorHeader

/-! # Exact descriptor-stream headers after occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Occurrence splitting produces exactly three route records per source
literal occurrence. -/
@[simp] theorem numericRouteDescriptors_formula_length
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.numericRouteDescriptors (formula source)).length =
      3 * PeriodicCNF.presentationLiteralCount source := by
  unfold PeriodicCNF.numericRouteDescriptors
  simp only [List.length_map, List.length_zipIdx]
  calc
    (PeriodicCNF.incidencesWithMetadata (formula source)).length =
        (formula source).incidenceGraph.edges.length :=
      (PeriodicCNF.incidenceGraph_edges_length_eq_metadata _).symm
    _ = PeriodicCNF.presentationLiteralCount (formula source) :=
      PeriodicCNF.incidenceGraph_edges_length _
    _ = 3 * PeriodicCNF.presentationLiteralCount source :=
      formula_presentationLiteralCount source

/-- Every emitted route record repeats the exact split-formula vertex count. -/
theorem numericRouteDescriptors_formula_vertexCounts
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.numericRouteDescriptors (formula source)).map
        PeriodicOrthocrossing.RouteDescriptor.vertexCount =
      List.replicate (3 * PeriodicCNF.presentationLiteralCount source)
        (source.clauses.length +
          2 * PeriodicCNF.presentationLiteralCount source) := by
  unfold PeriodicCNF.numericRouteDescriptors
  rw [List.map_map]
  simp only [Function.comp_def,
    numericRouteDescriptor_formula_vertexCount]
  change List.map
      (Function.const
        (CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
        (source.clauses.length +
          2 * PeriodicCNF.presentationLiteralCount source))
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx = _
  rw [List.map_const]
  congr 1
  simpa [PeriodicCNF.numericRouteDescriptors] using
    numericRouteDescriptors_formula_length source

/-- Every emitted route record repeats the common route count `3n`. -/
theorem numericRouteDescriptors_formula_edgeCounts
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (PeriodicCNF.numericRouteDescriptors (formula source)).map
        PeriodicOrthocrossing.RouteDescriptor.edgeCount =
      List.replicate (3 * PeriodicCNF.presentationLiteralCount source)
        (3 * PeriodicCNF.presentationLiteralCount source) := by
  unfold PeriodicCNF.numericRouteDescriptors
  rw [List.map_map]
  simp only [Function.comp_def,
    numericRouteDescriptor_formula_edgeCount]
  change List.map
      (Function.const
        (CNFIncidence (ThreeOccurrenceVariable Variable) × Nat)
        (3 * PeriodicCNF.presentationLiteralCount source))
      (PeriodicCNF.incidencesWithMetadata (formula source)).zipIdx = _
  rw [List.map_const]
  congr 1
  simpa [PeriodicCNF.numericRouteDescriptors] using
    numericRouteDescriptors_formula_length source

end PeriodicThreeSATThree
end LeanTrominoes
