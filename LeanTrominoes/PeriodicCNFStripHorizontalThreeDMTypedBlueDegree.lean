/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree

/-! # Typed blue degrees behind computed horizontal 3DM positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMPositionProblemComputed_blue_degree_idxOf
    (source : PeriodicCNF Nat)
    (element : PeriodicPlanarOneInThreeToThreeDM.BlueElement RoutedVariable)
    (member : element ∈ horizontalThreeDMBlueElementsComputed source) :
    (horizontalThreeDMPositionProblemComputed source).degree .blue
        ((horizontalThreeDMBlueElementsComputed source).idxOf element) =
      ((PeriodicPlanarOneInThreeToThreeDM.problem
        (horizontalThreeDMTypedSourceComputed source)).blueIncidences
          element).length := by
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_blue_degree
    (horizontalThreeDMTypedSourceComputed source) element member

end PeriodicCNFStripReduction
end LeanTrominoes
