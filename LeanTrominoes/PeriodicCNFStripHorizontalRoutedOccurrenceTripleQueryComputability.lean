/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceNormalizedSourceComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRoutedOccurrenceTripleComputability

/-! # Computability of routed-triple queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalRoutedOccurrenceTripleInputComputed_primrec :
    Primrec horizontalRoutedOccurrenceTripleInputComputed := by
  exact Primrec.pair
    (Primrec.pair
      (Primrec.pair
        horizontalVariableTypedIncidenceNormalizedSourceComputed_primrec
        (Primrec.snd.comp
          horizontalVariableTypedIncidenceSourceAtomComputed_primrec))
      (Primrec.snd.comp
        horizontalVariableTypedIncidenceMetadataComputed_primrec))
    Primrec.snd

theorem horizontalRoutedOccurrenceTripleQueryComputed_primrec :
    Primrec horizontalRoutedOccurrenceTripleQueryComputed := by
  exact routedOccurrenceTriple_primrec.comp
    horizontalRoutedOccurrenceTripleInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
