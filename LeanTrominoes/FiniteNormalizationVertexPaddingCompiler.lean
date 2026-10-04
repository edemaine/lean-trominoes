/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteAffineVertexRequestPaddingCompiler
import LeanTrominoes.FiniteNormalizationVertexRequestPadding

/-! # Reuse the original vertex request machine for the finite padded input -/
noncomputable section
namespace LeanTrominoes.FiniteNormalizationVertexPaddingCompiler
open _root_.Computability Turing Gadget PeriodicCNFStripReduction
open PeriodicThreeDM.NormalizationCompiler

def computableInPolyTime {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (inputs : List Symbol → Input) (units : List Symbol → List Unit)
    (unitLength : ∀ source,(units source).length=(inputs source).drawing.gridSize)
    (zero : ∀ source,(inputs source).problem.ZeroOffsets)
    (vertexLength : ∀ source,(inputs source).drawing.vertexPositions.length=
      (inputs source).problem.incidenceGraph.vertices.length)
    (bounds : ∀ source vertex,vertex∈(inputs source).problem.contractedGraph.vertices →
      let point := (inputs source).drawing.vertexPosition (inputs source).problem.incidenceGraph vertex
      0≤point.1 ∧ point.1<((inputs source).drawing.gridSize:Int) ∧
      0≤point.2 ∧ point.2<((inputs source).drawing.gridSize:Int))
    (emitter : TM2ComputableInPolyTime id id
      (fun source => (inputs source).problem.contractedGraph.vertices.flatMap
        (sparseBoundedInputVertexRequestRecord (inputs source))))
    (unitCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id id
      (fun source => (inputs source).finitePad.problem.contractedGraph.vertices.flatMap
        (sparseBoundedInputVertexRequestRecord (inputs source).finitePad)) := by
  let compiler := FiniteAffineVertexRequestPaddingCompiler.computableInPolyTime
    (fun source => (inputs source).problem.contractedGraph.vertices) units
    (fun source vertex => ((inputs source).drawing.vertexPosition
      (inputs source).problem.incidenceGraph vertex).1.toNat)
    (fun source vertex => 2*(inputs source).drawing.gridSize-
      ((inputs source).drawing.vertexPosition (inputs source).problem.incidenceGraph vertex).2.toNat-1)
    (fun source vertex => finalVertexCellType (inputs source) vertex) emitter unitCompiler
  apply TM2ComputableInPolyTime.of_eq compiler
  intro source
  rw [unitLength]
  apply List.flatMap_congr
  intro vertex member
  exact (sparseBoundedInputVertexRequestRecord_finitePad (inputs source) (zero source)
    (vertexLength source) member (bounds source vertex member)).symm
end LeanTrominoes.FiniteNormalizationVertexPaddingCompiler
