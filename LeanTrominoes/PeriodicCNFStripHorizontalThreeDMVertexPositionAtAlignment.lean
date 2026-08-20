/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtLengths

/-! # List alignment for pointwise horizontal 3DM positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

private theorem map_range_getD {Value : Type}
    (values : List Value) (default : Value) :
    (List.range values.length).map
        (fun index => values.getD index default) =
      values := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    have indexLt : index < values.length := by
      simpa using leftBound
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ indexLt]

/-- The assembled executable position list is exactly the pointwise table
mapped over the executable incidence-graph vertex order. -/
theorem horizontalThreeDMVertexPositionsComputed_eq_map_positionAt
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVertexPositionsComputed source =
      (horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices.map
        (horizontalThreeDMVertexPositionAtComputed source) := by
  unfold horizontalThreeDMVertexPositionsComputed
    horizontalThreeDMColoredPositionsComputed
    horizontalThreeDMGreenBluePositionsComputed
    PeriodicThreeDM.incidenceGraph PeriodicThreeDM.tripleVertices
    PeriodicThreeDM.elementVertices PeriodicThreeDM.coloredElementVertices
  simp only [List.map_append, List.map_map, Function.comp_def,
    horizontalThreeDMVertexPositionAtComputed]
  rw [← horizontalThreeDMTriplePositionsComputed_length,
    ← horizontalThreeDMRedPositionsComputed_length,
    ← horizontalThreeDMGreenPositionsComputed_length,
    ← horizontalThreeDMBluePositionsComputed_length,
    map_range_getD, map_range_getD, map_range_getD, map_range_getD]
  simp only [List.append_assoc]

end PeriodicCNFStripReduction
end LeanTrominoes
