/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMPeriodComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsComputability
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledEdgeRouteData
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler

/-! # Executable horizontal 3DM drawing and normalization input -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The complete proof-free horizontal periodic grid drawing. -/
def horizontalThreeDMDrawingComputed
    (source : PeriodicCNF Nat) : PeriodicGridDrawing :=
  PeriodicGridDrawing.equivData.symm
    (horizontalThreeDMGridSizePredComputed source,
      horizontalThreeDMVertexPositionsComputed source,
      horizontalThreeDMEdgeRoutesComputed source)

/-- The finite problem-and-drawing pair consumed by rectangular
normalization. -/
def horizontalNormalizationInputComputed
    (source : PeriodicCNF Nat) :
    PeriodicThreeDM.NormalizationCompiler.Input :=
  PeriodicThreeDM.NormalizationCompiler.Input.equivData.symm
    (horizontalThreeDMProblemComputed source,
      horizontalThreeDMDrawingComputed source)

end PeriodicCNFStripReduction
end LeanTrominoes
