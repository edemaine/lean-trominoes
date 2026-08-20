/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtAlignment
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingData

/-! # Pointwise executable horizontal 3DM drawing lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalThreeDMPositionProblemComputed_eq
    (source : PeriodicCNF Nat) :
    horizontalThreeDMPositionProblemComputed source =
      horizontalThreeDMProblemComputed source := by
  have decidableEqCoherence :
      horizontalThreeDMTripleVariableDecidableEq =
        horizontalRibbonRoutedVariableDecidableEq :=
    Subsingleton.elim _ _
  exact congrArg
    (fun decEq : DecidableEq RoutedVariable =>
      @PeriodicPlanarOneInThreeToThreeDM.encodedProblem
        RoutedVariable decEq
        (horizontalNormalizedRoutedFormulaComputed source).erase)
    decidableEqCoherence

/-- On every listed numeric incidence vertex, executable drawing lookup is
the corresponding entry of the proof-free pointwise table. -/
theorem horizontalThreeDMDrawingComputed_vertexPosition_eq_positionAt
    (source : PeriodicCNF Nat)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈
      (horizontalThreeDMProblemComputed source).incidenceGraph.vertices) :
    (horizontalThreeDMDrawingComputed source).vertexPosition
        (horizontalThreeDMProblemComputed source).incidenceGraph vertex =
      horizontalThreeDMVertexPositionAtComputed source vertex := by
  have problemEq := horizontalThreeDMPositionProblemComputed_eq source
  have member' : vertex ∈
      (horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices := by
    rw [problemEq]
    exact member
  have indexLt :
      (horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices.idxOf
          vertex <
        (horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr member'
  have mappedIndexLt :
      (horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices.idxOf
          vertex <
        ((horizontalThreeDMPositionProblemComputed source).incidenceGraph.vertices.map
          (horizontalThreeDMVertexPositionAtComputed source)).length := by
    simpa only [List.length_map] using indexLt
  rw [← problemEq]
  unfold PeriodicGridDrawing.vertexPosition
  rw [horizontalThreeDMDrawingComputed_vertexPositions,
    horizontalThreeDMVertexPositionsComputed_eq_map_positionAt,
    List.getD_eq_getElem _ _ mappedIndexLt]
  simp only [List.getElem_map]
  exact congrArg (horizontalThreeDMVertexPositionAtComputed source)
    (List.idxOf_get indexLt)

end PeriodicCNFStripReduction
end LeanTrominoes
