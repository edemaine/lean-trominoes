/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalColoredPositionListBridge

/-! # Identification of named and original assembled vertex-position data -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem assembledVertexPositionListData_eq_assembled
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) :
    assembledVertexPositionListData source variableOrigin clauseOrigin =
      assembledVertexPositionsData source variableOrigin clauseOrigin := by
  unfold assembledVertexPositionListData assembledTriplePositionsData
    assembledVertexPositionsData
  rw [assembledColoredElementPositionsData_eq]
  simp only [List.append_assoc]

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
