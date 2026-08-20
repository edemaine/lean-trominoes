/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceMetadataComputability

/-! # Computability of complete occurrence-route queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableOccurrenceRouteQueryComputed_primrec :
    Primrec horizontalVariableOccurrenceRouteQueryComputed := by
  exact Primrec.pair
    horizontalVariableTypedIncidenceMetadataComputed_primrec Primrec.snd

end PeriodicCNFStripReduction
end LeanTrominoes
