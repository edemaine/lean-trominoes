/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionAtData

/-! # Length alignment for pointwise horizontal 3DM positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

@[simp] theorem horizontalThreeDMTriplePositionsComputed_length
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMTriplePositionsComputed source).length =
      (horizontalThreeDMPositionProblemComputed source).triples.length := by
  simp [horizontalThreeDMTriplePositionsComputed,
    horizontalThreeDMPositionProblemComputed,
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.problem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode]

@[simp] theorem horizontalThreeDMRedPositionsComputed_length
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMRedPositionsComputed source).length =
      (horizontalThreeDMPositionProblemComputed source).elementCount .red := by
  simp [horizontalThreeDMRedPositionsComputed,
    horizontalThreeDMPositionProblemComputed,
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.problem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,
    PeriodicThreeDM.elementCount]

@[simp] theorem horizontalThreeDMGreenPositionsComputed_length
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMGreenPositionsComputed source).length =
      (horizontalThreeDMPositionProblemComputed source).elementCount .green := by
  simp [horizontalThreeDMGreenPositionsComputed,
    horizontalThreeDMPositionProblemComputed,
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.problem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,
    PeriodicThreeDM.elementCount]

@[simp] theorem horizontalThreeDMBluePositionsComputed_length
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMBluePositionsComputed source).length =
      (horizontalThreeDMPositionProblemComputed source).elementCount .blue := by
  simp [horizontalThreeDMBluePositionsComputed,
    horizontalThreeDMPositionProblemComputed,
    PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.problem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,
    PeriodicThreeDM.elementCount]

end PeriodicCNFStripReduction
end LeanTrominoes
