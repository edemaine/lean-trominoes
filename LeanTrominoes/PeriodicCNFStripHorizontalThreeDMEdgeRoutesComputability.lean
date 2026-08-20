/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteAtTagComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceTagsComputability

/-! # Computability of complete stored horizontal 3DM edge routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalThreeDMEdgeRoutesComputed_primrec :
    Primrec horizontalThreeDMEdgeRoutesComputed := by
  exact Primrec.list_map horizontalThreeDMIncidenceTagsComputed_primrec
    (horizontalAssembledRouteAtTagComputed_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

end PeriodicCNFStripReduction
end LeanTrominoes
