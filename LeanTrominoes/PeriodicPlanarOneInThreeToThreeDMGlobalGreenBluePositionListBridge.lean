/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalVertexPositionListData

/-! # Expansion of the named green-and-blue position block -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem assembledGreenBlueElementPositionsData_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    assembledGreenBlueElementPositionsData source variableOrigin clauseOrigin =
      (greenElements source).map
          (assembledGreenElementPositionData source variableOrigin clauseOrigin) ++
        (blueElements source).map
          (assembledBlueElementPositionData source variableOrigin clauseOrigin) := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
