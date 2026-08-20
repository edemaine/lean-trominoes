/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodedDegree

/-! # Typed red degrees behind computed horizontal 3DM positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMPositionProblemComputed_red_degree_idxOf
    (source : PeriodicCNF Nat)
    (element : PeriodicPlanarOneInThreeToThreeDM.RedElement RoutedVariable)
    (member : element ∈ horizontalThreeDMRedElementsComputed source) :
    (horizontalThreeDMPositionProblemComputed source).degree .red
        ((horizontalThreeDMRedElementsComputed source).idxOf element) =
      ((PeriodicPlanarOneInThreeToThreeDM.problem
        (horizontalThreeDMTypedSourceComputed source)).redIncidences
          element).length := by
  exact PeriodicPlanarOneInThreeToThreeDM.encodedProblem_red_degree
    (horizontalThreeDMTypedSourceComputed source) element member

end PeriodicCNFStripReduction
end LeanTrominoes
