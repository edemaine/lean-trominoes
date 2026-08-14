/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterization

/-!
# Data-only compiler for normalized rectangular 3DM drawings

This is the executable rectangular counterpart of `compile`.  It consumes
only the finite 3DM and grid-drawing data, while a final definitional theorem
connects it to the proof-backed strip construction.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM
namespace NormalizationCompiler

/-- Row count of the rectangular output, including two blank seam rows. -/
def finalStripHeight (input : Input) : Nat :=
  3 * finalNormalizationPeriod input + 1

/-- Final normalized vertices placed in the rectangular raster. -/
def finalStripVertexAssignments (input : Input) :
    List NormalizedCellAssignment :=
  input.problem.contractedGraph.vertices.map fun vertex =>
    (stripRasterLocation (finalNormalizationPeriod input)
      (finalNormalizationPosition input vertex),
      finalVertexCellType input vertex)

/-- Final normalized route interiors placed in the rectangular raster. -/
def finalStripRouteAssignments (input : Input) :
    List NormalizedCellAssignment :=
  input.problem.contractedEdges.flatMap fun edge =>
    stripRouteInteriorAssignments (finalNormalizationPeriod input)
      edge.color (finalNormalizationRoute input edge)

/-- Prioritized nonblank assignments for the rectangular raster. -/
def finalStripCellAssignments (input : Input) :
    List NormalizedCellAssignment :=
  finalStripVertexAssignments input ++ finalStripRouteAssignments input

/-- Total rectangular-raster lookup with a blank fallback. -/
def finalStripCellTypeAt (input : Input) (location : Cell) :
    OrthogonalCellType :=
  ((finalStripCellAssignments input).lookup location).getD .blank

/-- Row-major cell array of width `P` and height `3P + 1`. -/
def finalStripCellTypes (input : Input) : List OrthogonalCellType :=
  rowMajorList (finalStripHeight input) (finalNormalizationPeriod input)
    fun horizontal vertical =>
      finalStripCellTypeAt input (horizontal, vertical)

/-- Shallow runtime name for the complete rectangular cell array. -/
def compiledStripCellTypes (input : Input) : List OrthogonalCellType :=
  finalStripCellTypes input

/-- The three finite fields of the rectangular output drawing. -/
def compileStripData (input : Input) :
    Nat × Nat × List OrthogonalCellType :=
  (finalNormalizationPeriod input - 1,
    3 * finalNormalizationPeriod input,
    compiledStripCellTypes input)

/-- Reconstruct a drawing from its three canonical finite fields. -/
def periodicOrthogonalStripDrawingFromData
    (data : Nat × Nat × List OrthogonalCellType) :
    PeriodicOrthogonalDrawing where
  horizontalPeriodPred := data.1
  verticalPeriodPred := data.2.1
  cellTypes := data.2.2

/-- Complete data-only rectangular normalized drawing compiler. -/
def compileStrip (input : Input) : PeriodicOrthogonalDrawing where
  horizontalPeriodPred := finalNormalizationPeriod input - 1
  verticalPeriodPred := 3 * finalNormalizationPeriod input
  cellTypes := compiledStripCellTypes input

/-- Canonical encoded-data implementation of the same compiler. -/
def computableCompileStrip (input : Input) : PeriodicOrthogonalDrawing :=
  periodicOrthogonalStripDrawingFromData (compileStripData input)

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
