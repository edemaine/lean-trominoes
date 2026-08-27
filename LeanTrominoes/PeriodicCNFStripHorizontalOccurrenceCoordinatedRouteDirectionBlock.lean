/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonRoutingFacts
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceStubDirectionData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubSemanticBridge

/-! # Compact complete horizontal occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The complete occurrence word is a finite variable-fan block, the compact
adjacent-direction corridor word, and a finite clause-fan block. -/
def horizontalOccurrenceCoordinatedDirections
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock) :
    List AxisDirection :=
  (horizontalOccurrenceVariableStubDirections input ++
      horizontalOccurrenceRibbonCorridorDirections input block) ++
    horizontalOccurrenceClauseStubDirections input

/-- Every successful horizontal occurrence lookup has a compact complete
coordinated route word. -/
theorem horizontalOccurrenceCoordinatedRoute_directionBlock_of_lookup
    (input : HorizontalOccurrenceColoredRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input.1 = some tagged) :
    ∃ block : HorizontalRoutedRouteDirectionBlock,
      unitSubdivisionDirections
          (horizontalOccurrenceCoordinatedRouteComputed input) =
        horizontalOccurrenceCoordinatedDirections input block := by
  rcases input with ⟨⟨⟨source, atom⟩, slot⟩, color⟩
  have occurrenceLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (horizontalNormalizedRoutedFormulaComputed source).erase
          atom slot = some tagged := by
    simpa only [horizontalOccurrenceLookupComputed,
      horizontalOccurrenceLookupInput,
      PeriodicPlanarOneInThreeToThreeDM.occurrenceAt] using lookup
  have semanticLookup :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (horizontalSemanticNormalizedRibbonSource source).erase
          atom slot = some tagged := by
    rw [← horizontalNormalizedRoutedFormulaComputed_eq_semanticData]
    exact occurrenceLookup
  have taggedFacts :=
    PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (horizontalSemanticNormalizedRibbonSource source).erase
      atom slot tagged semanticLookup
  have atomMember :
      atom ∈ occurringVariables
        (horizontalSemanticNormalizedRibbonSource source).erase := by
    rw [← taggedFacts.2]
    exact
      PeriodicOneInThreeToThreeDM.atom_mem_occurringVariables_of_tagged_mem
        (horizontalSemanticNormalizedRibbonSource source).erase
        tagged taggedFacts.1
  have slotMember :
      slot ∈ usedSlots
        (horizontalSemanticNormalizedRibbonSource source).erase atom := by
    apply (occurrenceAt_isSome_eq_true_iff_mem_usedSlots
      (horizontalSemanticNormalizedRibbonSource source).erase atom slot).mp
    unfold PeriodicPlanarOneInThreeToThreeDM.occurrenceAt
    rw [semanticLookup]
    rfl
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨atomMember, slotMember⟩⟩
  let planar := horizontalSemanticNormalizedPlanarPresentation source
  have width :=
    horizontalSemanticNormalizedRibbonSource_widthAtMostThree source
  have compatible :=
    horizontalSemanticNormalizedRibbonSource_fansCompatible source
  have variableEq :
      horizontalOccurrenceVariableStubComputed
          ((((source, atom), slot), color)) =
        occurrenceCoordinatedRibbonVariableStub planar entry color := by
    simpa only [entry, planar] using
      horizontalOccurrenceVariableStubComputed_eq_semantic
        source entry color
  have corridorEq :
      horizontalOccurrenceRibbonCorridorCoreComputed
          ((((source, atom), slot), color)) =
        occurrenceRibbonCorridorCore planar entry color := by
    simpa only [entry, planar] using
      horizontalOccurrenceRibbonCorridorCoreComputed_eq_semantic
        source entry color
  have clauseEq :
      horizontalOccurrenceClauseStubComputed
          ((((source, atom), slot), color)) =
        occurrenceCoordinatedRibbonClauseStub planar entry color := by
    simpa only [entry, planar] using
      horizontalOccurrenceClauseStubComputed_eq_semantic
        source entry color
  have variableEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry color
  have corridorEndpoints :=
    occurrenceRibbonCorridorCore_endpoints planar entry color
  have clauseEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      planar width compatible entry color
  rw [← variableEq] at variableEndpoints
  rw [← corridorEq] at corridorEndpoints
  rw [← clauseEq] at clauseEndpoints
  have variableNonempty :
      horizontalOccurrenceVariableStubComputed
          ((((source, atom), slot), color)) ≠ [] := by
    intro empty
    rw [empty] at variableEndpoints
    simp at variableEndpoints
  have firstBoundary :
      (horizontalOccurrenceVariableStubComputed
          ((((source, atom), slot), color))).getLast? =
        (horizontalOccurrenceRibbonCorridorCoreComputed
          ((((source, atom), slot), color))).head? :=
    variableEndpoints.2.trans corridorEndpoints.1.symm
  let firstJoin := joinAtEndpoint
    (horizontalOccurrenceVariableStubComputed
      ((((source, atom), slot), color)))
    (horizontalOccurrenceRibbonCorridorCoreComputed
      ((((source, atom), slot), color)))
  have firstJoinHead := joinAtEndpoint_head?
    (second := horizontalOccurrenceRibbonCorridorCoreComputed
      ((((source, atom), slot), color)))
    variableEndpoints.1
  change firstJoin.head? = _ at firstJoinHead
  have firstJoinNonempty : firstJoin ≠ [] := by
    intro empty
    rw [empty] at firstJoinHead
    simp at firstJoinHead
  have firstJoinLast :
      firstJoin.getLast? =
        (horizontalOccurrenceRibbonCorridorCoreComputed
          ((((source, atom), slot), color))).getLast? := by
    change (joinAtEndpoint
        (horizontalOccurrenceVariableStubComputed
          ((((source, atom), slot), color)))
        (horizontalOccurrenceRibbonCorridorCoreComputed
          ((((source, atom), slot), color)))).getLast? = _
    exact (joinAtEndpoint_getLast?
      variableEndpoints.2 corridorEndpoints.1 corridorEndpoints.2).trans
        corridorEndpoints.2.symm
  have secondBoundary :
      firstJoin.getLast? =
        (horizontalOccurrenceClauseStubComputed
          ((((source, atom), slot), color))).head? :=
    firstJoinLast.trans
      (corridorEndpoints.2.trans clauseEndpoints.1.symm)
  rcases horizontalOccurrenceRibbonCorridor_directionBlock_of_lookup
      ((((source, atom), slot), color)) tagged lookup with
    ⟨block, corridorDirections⟩
  refine ⟨block, ?_⟩
  unfold horizontalOccurrenceCoordinatedRouteComputed
    horizontalOccurrenceCoordinatedDirections
  change unitSubdivisionDirections
      (joinAtEndpoint firstJoin
        (horizontalOccurrenceClauseStubComputed
          ((((source, atom), slot), color)))) = _
  rw [unitSubdivisionDirections_joinAtEndpoint
    firstJoinNonempty secondBoundary]
  change unitSubdivisionDirections
      (joinAtEndpoint
        (horizontalOccurrenceVariableStubComputed
          ((((source, atom), slot), color)))
        (horizontalOccurrenceRibbonCorridorCoreComputed
          ((((source, atom), slot), color)))) ++ _ = _
  rw [unitSubdivisionDirections_joinAtEndpoint
    variableNonempty firstBoundary]
  rw [unitSubdivisionDirections_horizontalOccurrenceVariableStubComputed,
    corridorDirections,
    unitSubdivisionDirections_horizontalOccurrenceClauseStubComputed]

end PeriodicCNFStripReduction
end LeanTrominoes

end
