/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteSomeComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceLookupComputability

/-! # Computability of total horizontal occurrence source routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

theorem horizontalOccurrenceSourceRouteComputed_primrec :
    Primrec horizontalOccurrenceSourceRouteComputed := by
  exact (Primrec.option_casesOn
    horizontalOccurrenceLookupComputed_primrec (Primrec.const [])
    horizontalOccurrenceSourceRouteSomeComputed_primrec.to₂).of_eq
      fun input => by
        generalize lookup : horizontalOccurrenceLookupComputed input = result
        cases result <;> simp [horizontalOccurrenceSourceRouteComputed,
          lookup]

end PeriodicCNFStripReduction
end LeanTrominoes
