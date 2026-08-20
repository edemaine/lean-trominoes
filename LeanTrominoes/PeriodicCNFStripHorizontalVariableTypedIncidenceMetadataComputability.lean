/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData

/-! # Computability of variable-incidence metadata projections -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableTypedIncidenceSourceAtomComputed_primrec :
    Primrec horizontalVariableTypedIncidenceSourceAtomComputed := by
  exact Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

theorem horizontalVariableTypedIncidenceMetadataComputed_primrec :
    Primrec horizontalVariableTypedIncidenceMetadataComputed := by
  exact Primrec.fst.comp Primrec.fst

end PeriodicCNFStripReduction
end LeanTrominoes
