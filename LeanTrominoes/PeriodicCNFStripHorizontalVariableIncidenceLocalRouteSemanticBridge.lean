/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteRouteDataBridge

/-! # Semantic bridge for horizontal finite variable-site routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidenceLocalRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (tripleMember : triple ∈ occurrenceTriples
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.1.2)
    (color : WireColor) :
    horizontalVariableIncidenceLocalRouteComputed
        (((source, entry.1.1), triple), color) =
      typedVariableSiteRoute
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 entry.atom_mem entry.1.2 entry.slot_mem
        triple tripleMember color := by
  unfold horizontalVariableIncidenceLocalRouteComputed
    horizontalVariableIncidenceLocalRouteInputComputed
  rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic
    source entry]
  exact variableSiteRouteData_sourceVariableRibbonFanData_eq
    (horizontalSemanticNormalizedPlanarPresentation source)
    entry triple tripleMember color

end PeriodicCNFStripReduction
end LeanTrominoes
