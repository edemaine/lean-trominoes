/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceTripleMembership
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceTypedDirectionBlockSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionBlock

/-! # Actual geometric words of canonical occurrence-triple blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Each genuine variable incidence is its finite prefix followed by the
coordinated route exactly at the routed triple for that color. -/
theorem horizontalOccurrenceTypedIncidenceRoute_directions
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (entryMember : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (tripleMember : triple ∈ occurrenceTriples
      (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2)
    (color : WireColor) :
    unitSubdivisionDirections (horizontalTypedIncidenceRouteComputed ((source, triple), color)) =
      horizontalVariableIncidencePrefixDirections (((source, entry.1), triple), color) ++
        if triple = routedOccurrenceTriple
            (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 color then
          unitSubdivisionDirections
            (horizontalOccurrenceCoordinatedRouteComputed (((source, entry.1), entry.2), color))
        else [] := by
  have globalMember := mem_triples_of_mem_occurrenceTriples
    (horizontalSemanticNormalizedRibbonSource source).erase entry entryMember triple tripleMember
  rcases occurrenceTriples_member_cases
      (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2 triple tripleMember with
    ⟨variant, localTriple, rfl⟩ | ⟨localTriple, rfl⟩
  · have directions := horizontalOrdinaryVariableTypedIncidenceRoute_directions
      source entry.1 entry.2 variant localTriple globalMember color
    dsimp only at directions
    simpa only [horizontalTypedIncidenceRouteComputed,
      horizontalVariableRoutePrefixQueryComputed_explicit,
      horizontalVariableOccurrenceRouteQueryComputed_explicit] using directions
  · have directions := horizontalFixedRedVariableTypedIncidenceRoute_directions
      source entry.1 entry.2 localTriple globalMember color
    dsimp only at directions
    simpa only [horizontalTypedIncidenceRouteComputed,
      horizontalVariableRoutePrefixQueryComputed_explicit,
      horizontalVariableOccurrenceRouteQueryComputed_explicit] using directions

/-- The local typed body shape is exactly the actual geometric route list,
in typed-triple and red/green/blue order. -/
theorem groupedVariableIncidenceTypedShapeBodies_eq_horizontalRoutes
    (source : PeriodicCNF Nat) (entry : RoutedVariable × OccurrenceSlot)
    (member : entry ∈ occurrenceEntries (horizontalSemanticNormalizedRibbonSource source).erase) :
    groupedVariableIncidenceTypedShapeBodies
      (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2
      (horizontalOccurrenceVariableRibbonFanDataComputed (source, entry.1))
      (fun color => unitSubdivisionDirections
        (horizontalOccurrenceCoordinatedRouteComputed (((source, entry.1), entry.2), color))) =
      (occurrenceTriples (horizontalSemanticNormalizedRibbonSource source).erase entry.1 entry.2).flatMap
        fun triple => incidenceColors.map fun color =>
          unitSubdivisionDirections (horizontalTypedIncidenceRouteComputed ((source, triple), color)) := by
  unfold groupedVariableIncidenceTypedShapeBodies
  apply List.flatMap_congr
  intro triple tripleMember
  apply List.map_congr_left
  intro color _colorMember
  rw [groupedVariableIncidenceTypedPrefixDirection_eq_horizontal]
  exact (horizontalOccurrenceTypedIncidenceRoute_directions source entry member triple tripleMember color).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
