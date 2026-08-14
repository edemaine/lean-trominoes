/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMRedPositionListComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMGreenBluePositionsComputability

/-! # Computability of the concrete colored-element position suffix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

def horizontalThreeDMColoredPositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  horizontalThreeDMRedPositionsComputed source ++
    horizontalThreeDMGreenBluePositionsComputed source

theorem horizontalThreeDMColoredPositionsComputed_primrec :
    Primrec horizontalThreeDMColoredPositionsComputed := by
  exact Primrec.list_append.comp
    horizontalThreeDMRedPositionsComputed_primrec
    horizontalThreeDMGreenBluePositionsComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
