/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseVertexInputData
import LeanTrominoes.PeriodicThreeDMVertexNormalizationEndpointOccurrences

/-! # Fundamental-square bounds for normalization compiler inputs -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- A compiler input obtained from a certified planar presentation reads each
contracted vertex from the original drawing's horizontal fundamental
interval. -/
theorem normalizationCompiler_inputOfPresentation_vertexPosition_horizontal_bounds
    {problem : PeriodicThreeDM}
    (planar : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    let input :=
      PeriodicThreeDM.NormalizationCompiler.inputOfPresentation planar
    0 ≤ (input.drawing.vertexPosition
        input.problem.incidenceGraph vertex).1 ∧
      (input.drawing.vertexPosition
          input.problem.incidenceGraph vertex).1 <
        (input.drawing.gridSize : Int) := by
  let input :=
    PeriodicThreeDM.NormalizationCompiler.inputOfPresentation planar
  have compilerMember : vertex ∈ input.problem.contractedGraph.vertices :=
    member
  have lookupEq :=
    normalizationCompiler_normalizationPosition0_eq_inputDrawing
      input compilerMember
  have bounds :=
    planar.normalizationPosition0_in_fundamental_square member
  have positionEq :
      planar.normalizationPosition0 vertex =
        input.drawing.vertexPosition input.problem.incidenceGraph vertex := by
    calc
      planar.normalizationPosition0 vertex =
          PeriodicThreeDM.NormalizationCompiler.normalizationPosition0
            input vertex := rfl
      _ = _ := lookupEq
  have gridEq :
      planar.contractedDrawing.gridSize = input.drawing.gridSize :=
    rfl
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare] at bounds
  rw [positionEq, gridEq] at bounds
  exact ⟨le_of_lt bounds.1, bounds.2.1⟩

end PeriodicCNFStripReduction
end LeanTrominoes
