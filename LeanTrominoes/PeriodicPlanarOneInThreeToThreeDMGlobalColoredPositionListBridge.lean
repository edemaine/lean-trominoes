/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalGreenBluePositionListBridge

/-! # Expansion of the named colored-element position block -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem assembledColoredElementPositionsData_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    assembledColoredElementPositionsData source variableOrigin clauseOrigin =
      (redElements source).map
          (assembledRedElementPositionData source variableOrigin clauseOrigin) ++
        (greenElements source).map
          (assembledGreenElementPositionData source variableOrigin clauseOrigin) ++
        (blueElements source).map
          (assembledBlueElementPositionData source variableOrigin clauseOrigin) := by
  unfold assembledColoredElementPositionsData
    assembledRedElementPositionsData
  rw [assembledGreenBlueElementPositionsData_eq]
  rw [List.append_assoc]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
