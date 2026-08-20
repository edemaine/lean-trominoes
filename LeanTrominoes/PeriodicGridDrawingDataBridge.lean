/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawing

/-! # Projection lemmas for canonical periodic grid-drawing data -/

namespace LeanTrominoes
namespace PeriodicGridDrawing

@[simp] theorem equivData_symm_gridSizePred
    (gridSizePred : Nat) (vertexPositions : List Cell)
    (edgeRoutes : List (List Cell)) :
    (equivData.symm
      (gridSizePred, vertexPositions, edgeRoutes)).gridSizePred =
        gridSizePred := by
  rfl

@[simp] theorem equivData_symm_vertexPositions
    (gridSizePred : Nat) (vertexPositions : List Cell)
    (edgeRoutes : List (List Cell)) :
    (equivData.symm
      (gridSizePred, vertexPositions, edgeRoutes)).vertexPositions =
        vertexPositions := by
  rfl

@[simp] theorem equivData_symm_edgeRoutes
    (gridSizePred : Nat) (vertexPositions : List Cell)
    (edgeRoutes : List (List Cell)) :
    (equivData.symm
      (gridSizePred, vertexPositions, edgeRoutes)).edgeRoutes =
        edgeRoutes := by
  rfl

end PeriodicGridDrawing
end LeanTrominoes
