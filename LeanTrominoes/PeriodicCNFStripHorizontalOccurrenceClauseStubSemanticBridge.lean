/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs

/-! # Semantic correctness of translated clause occurrence stubs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

theorem occurrenceSourceRoute_getLast?_eq_clauseTarget
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (occurrenceSourceRoute presentation entry).getLast? =
      some (occurrenceSourceClauseTarget presentation entry) := by
  let data := occurrenceSpliceData presentation entry
  simpa [occurrenceSourceRoute, occurrenceSourceClauseTarget, data] using
    data.routeLast

end PeriodicPlanarOneInThreeToThreeDM

namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseCenterComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceClauseCenterComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceSourceClauseTarget
        (horizontalSemanticNormalizedPlanarPresentation source) entry := by
  unfold horizontalOccurrenceClauseCenterComputed polylineLastD
  rw [horizontalOccurrenceSourceRouteComputed_eq_semantic,
    List.getLastD_eq_getLast?,
    occurrenceSourceRoute_getLast?_eq_clauseTarget]
  rfl

theorem horizontalOccurrenceClauseStubComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceClauseStubComputed
        (((source, entry.1.1), entry.1.2), color) =
      occurrenceCoordinatedRibbonClauseStub
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry color := by
  unfold horizontalOccurrenceClauseStubComputed
    occurrenceCoordinatedRibbonClauseStub
  rw [horizontalOccurrenceClauseCenterComputed_eq_semantic,
    horizontalOccurrenceClauseCoordinatedRouteComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
