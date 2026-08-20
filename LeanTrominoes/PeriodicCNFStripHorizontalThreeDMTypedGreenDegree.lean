/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree

/-! # Typed green degrees behind computed horizontal 3DM positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMPositionProblemComputed_green_degree_idxOf
    (source : PeriodicCNF Nat)
    (element : PeriodicPlanarOneInThreeToThreeDM.GreenElement RoutedVariable)
    (member : element ∈ horizontalThreeDMGreenElementsComputed source) :
    (horizontalThreeDMPositionProblemComputed source).degree .green
        ((horizontalThreeDMGreenElementsComputed source).idxOf element) =
      ((PeriodicPlanarOneInThreeToThreeDM.problem
        (horizontalThreeDMTypedSourceComputed source)).greenIncidences
          element).length := by
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_green_degree
    (horizontalThreeDMTypedSourceComputed source) element member

end PeriodicCNFStripReduction
end LeanTrominoes
