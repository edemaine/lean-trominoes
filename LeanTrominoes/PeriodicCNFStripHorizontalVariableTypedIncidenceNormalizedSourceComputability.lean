/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceMetadataComputability

/-! # Computability of normalized variable-incidence sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableTypedIncidenceNormalizedSourceComputed_primrec :
    Primrec horizontalVariableTypedIncidenceNormalizedSourceComputed := by
  exact (PositionedPeriodicCNF.erase_primrec.comp
    horizontalNormalizedRoutedFormulaComputed_primrec).comp
      (Primrec.fst.comp
        horizontalVariableTypedIncidenceSourceAtomComputed_primrec)

end PeriodicCNFStripReduction
end LeanTrominoes
