/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMGreenPositionListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMBluePositionListComputability

/-! # Computability of the concrete green-and-blue position suffix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

def horizontalThreeDMGreenBluePositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMGreenPositionsComputed source ++
    horizontalThreeDMBluePositionsComputed source

theorem horizontalThreeDMGreenBluePositionsComputed_primrec :
    Primrec horizontalThreeDMGreenBluePositionsComputed := by
  exact Primrec.list_append.comp
    horizontalThreeDMGreenPositionsComputed_primrec
    horizontalThreeDMBluePositionsComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
