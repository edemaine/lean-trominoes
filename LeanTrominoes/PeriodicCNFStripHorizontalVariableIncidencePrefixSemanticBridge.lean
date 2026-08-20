/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidenceLocalRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMOriginSemanticBridge

/-! # Semantic bridge for translated horizontal variable prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableIncidencePrefixComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (tripleMember : triple ∈ occurrenceTriples
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.1.2)
    (color : WireColor) :
    horizontalVariableIncidencePrefixComputed
        (((source, entry.1.1), triple), color) =
      PeriodicOrthocrossing.translatePolyline
        ((coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible).variableOrigin entry.1.1)
        (typedVariableSiteRoute
          (horizontalSemanticNormalizedRibbonSource source).erase
          entry.1.1 entry.atom_mem entry.1.2 entry.slot_mem
          triple tripleMember color) := by
  unfold horizontalVariableIncidencePrefixComputed
    horizontalVariableIncidenceOriginComputed
  rw [horizontalVariableIncidenceLocalRouteComputed_eq_semantic,
    horizontalThreeDMVariableOriginComputed_eq_routing]

end PeriodicCNFStripReduction
end LeanTrominoes
