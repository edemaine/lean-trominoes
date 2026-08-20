/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceMetadataComputability

/-! # Computability of variable-prefix queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableRoutePrefixQueryComputed_primrec :
    Primrec horizontalVariableRoutePrefixQueryComputed := by
  exact Primrec.pair
    (Primrec.pair
      horizontalVariableTypedIncidenceSourceAtomComputed_primrec
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd

end PeriodicCNFStripReduction
end LeanTrominoes
