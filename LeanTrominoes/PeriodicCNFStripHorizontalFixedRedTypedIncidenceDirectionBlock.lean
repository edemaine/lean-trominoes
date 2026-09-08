/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.PeriodicCNFStripHorizontalFixedRedIncidencePrefixSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonRoutingFacts
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidenceQuerySemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalVariableTypedIncidenceDirectionBlockData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes

/-! # Compact fixed-red horizontal variable incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- The actual typed incidence word is its finite prefix followed by the
coordinated route exactly when this is the routed occurrence triple. -/
theorem horizontalFixedRedVariableTypedIncidenceRoute_directions
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member : Triple.fixedRed atom slot localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    let input : HorizontalVariableTypedIncidenceRouteInput :=
      ((((source, atom), slot),
        Triple.fixedRed atom slot localTriple), color)
    unitSubdivisionDirections (horizontalVariableTypedIncidenceRouteComputed input) =
      horizontalVariableIncidencePrefixDirections (horizontalVariableRoutePrefixQueryComputed input) ++
        if Triple.fixedRed atom slot localTriple = routedOccurrenceTriple
            (horizontalSemanticNormalizedRibbonSource source).erase atom slot color then
          unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (horizontalVariableOccurrenceRouteQueryComputed input))
        else [] := by
  dsimp only
  let typed : Triple RoutedVariable :=
    .fixedRed atom slot localTriple
  let input : HorizontalVariableTypedIncidenceRouteInput :=
    ((((source, atom), slot), typed), color)
  change unitSubdivisionDirections (horizontalVariableTypedIncidenceRouteComputed input) =
    horizontalVariableIncidencePrefixDirections (((source, atom), typed), color) ++
        if typed = routedOccurrenceTriple
            (horizontalSemanticNormalizedRibbonSource source).erase atom slot color then
          unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (horizontalVariableOccurrenceRouteQueryComputed input))
        else []
  let location := fixedRedTriple_location
    (horizontalSemanticNormalizedRibbonSource source).erase
    atom slot localTriple member
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨location.1, location.2.1⟩⟩
  have width :=
    horizontalSemanticNormalizedRibbonSource_widthAtMostThree source
  have compatible :=
    horizontalSemanticNormalizedRibbonSource_fansCompatible source
  have routedQuery :
      horizontalRoutedOccurrenceTripleQueryComputed input =
        routedOccurrenceTriple
          (horizontalSemanticNormalizedRibbonSource source).erase
          atom slot color := by
    simpa only [input, entry, typed] using
      horizontalRoutedOccurrenceTripleQueryComputed_eq_semantic
        source entry typed color
  by_cases isRouted :
      typed = routedOccurrenceTriple
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot color
  ·
    have prefixEq :=
      horizontalVariableIncidencePrefixComputed_eq_assembledFixedRed
        source width compatible atom slot localTriple member color
    have occurrenceEq :=
      horizontalVariableOccurrenceRouteComputed_eq_routing
        source width compatible entry typed color
    have prefixLast :=
      assembledFixedRedPrefix_getLast_routed
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        atom slot localTriple member color isRouted
    dsimp only at prefixLast
    have prefixLastComputed :=
      (congrArg (fun route : List Cell => route.getLast?) prefixEq).trans
        prefixLast
    have occurrenceHead :=
      ((coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible).route_endpoints entry color).1
    have occurrenceHeadComputed :=
      (congrArg (fun route : List Cell => route.head?) occurrenceEq).trans
        occurrenceHead
    have prefixNonempty :
        horizontalVariableIncidencePrefixComputed
            (((source, atom), typed), color) ≠ [] := by
      intro empty
      rw [empty] at prefixLastComputed
      simp at prefixLastComputed
    have boundary := prefixLastComputed.trans occurrenceHeadComputed.symm
    unfold horizontalVariableTypedIncidenceRouteComputed
    change unitSubdivisionDirections
        (if typed = horizontalRoutedOccurrenceTripleQueryComputed input then
          joinAtEndpoint
            (horizontalVariableIncidencePrefixComputed (((source, atom), typed), color))
            (horizontalOccurrenceCoordinatedRouteComputed
              (horizontalVariableOccurrenceRouteQueryComputed input))
        else horizontalVariableIncidencePrefixComputed (((source, atom), typed), color)) =
      horizontalVariableIncidencePrefixDirections (((source, atom), typed), color) ++
        if typed = routedOccurrenceTriple
            (horizontalSemanticNormalizedRibbonSource source).erase atom slot color then
          unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (horizontalVariableOccurrenceRouteQueryComputed input))
        else []
    rw [routedQuery]
    simp only [if_pos isRouted]
    rw [unitSubdivisionDirections_joinAtEndpoint prefixNonempty boundary,
      unitSubdivisionDirections_horizontalVariableIncidencePrefixComputed]
  · unfold horizontalVariableTypedIncidenceRouteComputed
    change unitSubdivisionDirections
        (if typed = horizontalRoutedOccurrenceTripleQueryComputed input then
          joinAtEndpoint
            (horizontalVariableIncidencePrefixComputed (((source, atom), typed), color))
            (horizontalOccurrenceCoordinatedRouteComputed
              (horizontalVariableOccurrenceRouteQueryComputed input))
        else horizontalVariableIncidencePrefixComputed (((source, atom), typed), color)) =
      horizontalVariableIncidencePrefixDirections (((source, atom), typed), color) ++
        if typed = routedOccurrenceTriple
            (horizontalSemanticNormalizedRibbonSource source).erase atom slot color then
          unitSubdivisionDirections (horizontalOccurrenceCoordinatedRouteComputed
            (horizontalVariableOccurrenceRouteQueryComputed input))
        else []
    rw [routedQuery]
    simp only [if_neg isRouted, List.append_nil]
    exact unitSubdivisionDirections_horizontalVariableIncidencePrefixComputed
      (((source, atom), typed), color)

/-- Every genuine typed incidence has its existing compact direction block. -/
theorem horizontalFixedRedVariableTypedIncidenceRoute_directionBlock
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member : Triple.fixedRed atom slot localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    let input : HorizontalVariableTypedIncidenceRouteInput :=
      ((((source, atom), slot),
        Triple.fixedRed atom slot localTriple), color)
    ∃ block : HorizontalVariableTypedIncidenceDirectionBlock,
      unitSubdivisionDirections
          (horizontalVariableTypedIncidenceRouteComputed input) =
        horizontalVariableTypedIncidenceDirections input block := by
  dsimp only
  have directions := horizontalFixedRedVariableTypedIncidenceRoute_directions source atom slot localTriple member color
  dsimp only at directions
  by_cases isRouted : Triple.fixedRed atom slot localTriple = routedOccurrenceTriple
      (horizontalSemanticNormalizedRibbonSource source).erase atom slot color
  · have location := fixedRedTriple_location
      (horizontalSemanticNormalizedRibbonSource source).erase atom slot localTriple member
    obtain ⟨tagged, lookup⟩ := exists_horizontalOccurrenceLookupComputed_of_slot_mem
      source atom slot location.2.1
    obtain ⟨block, occurrenceDirections⟩ := horizontalOccurrenceCoordinatedRoute_directionBlock_of_lookup
      (((source, atom), slot), color) tagged lookup
    refine ⟨.routed block, ?_⟩
    rw [directions, if_pos isRouted]
    simp only [horizontalVariableTypedIncidenceDirections,
      horizontalVariableOccurrenceRouteQueryComputed, horizontalVariableTypedIncidenceMetadataComputed]
    rw [occurrenceDirections]
  · refine ⟨.local, ?_⟩
    rw [directions, if_neg isRouted, List.append_nil]
    rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
