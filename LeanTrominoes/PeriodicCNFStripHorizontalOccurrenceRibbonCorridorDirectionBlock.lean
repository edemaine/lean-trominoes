/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSlotActivitySemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorDirectionData

/-! # Compact horizontal occurrence ribbon corridors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Apply the adjacent-pair ribbon table to one compact horizontal source
direction block on its computed physical lane. -/
def horizontalOccurrenceRibbonCorridorDirections
    (input : HorizontalOccurrenceColoredRouteInput)
    (block : HorizontalRoutedRouteDirectionBlock) :
    List AxisDirection :=
  ribbonCorridorDirectionWord
    (horizontalOccurrenceRibbonLaneComputed input)
    (horizontalOccurrenceSourceDirections block)

/-- The actual corridor word is the ribbon table applied to the selected
unit-source word on this occurrence's physical lane. -/
theorem horizontalOccurrenceRibbonCorridor_directions_of_lookup
    (input : HorizontalOccurrenceColoredRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input.1 = some tagged) :
    unitSubdivisionDirections (horizontalOccurrenceRibbonCorridorCoreComputed input) =
      ribbonCorridorDirectionWord (horizontalOccurrenceRibbonLaneComputed input)
        (unitSubdivisionDirections (horizontalOccurrenceUnitSourceRouteComputed input.1)) := by
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
  have computedRouteEq :
      horizontalOccurrenceUnitSourceRouteComputed ((source, atom), slot) =
        occurrenceUnitSourceRoute
          (horizontalSemanticNormalizedPlanarPresentation source)
          entry := by
    simpa only [entry] using
      horizontalOccurrenceUnitSourceRouteComputed_eq_semantic source entry
  have computedUnitSteps :
      (horizontalOccurrenceUnitSourceRouteComputed
          ((source, atom), slot)).IsChain AxisDirection.IsUnitAxisStep := by
    rw [computedRouteEq]
    exact occurrenceUnitSourceRoute_unitSteps
      (horizontalSemanticNormalizedPlanarPresentation source) entry
  unfold horizontalOccurrenceRibbonCorridorCoreComputed
    horizontalOccurrenceRibbonCorridorInputComputed
  simp only
  rw [unitSubdivisionDirections_ribbonCorridorCore_of_unitSteps
    _ _ computedUnitSteps]

/-- Every successful horizontal occurrence lookup expands its compact source
block through the finite adjacent-direction ribbon table. -/
theorem horizontalOccurrenceRibbonCorridor_directionBlock_of_lookup
    (input : HorizontalOccurrenceColoredRouteInput)
    (tagged : PeriodicOneInThreeToThreeDM.TaggedOccurrence RoutedVariable)
    (lookup : horizontalOccurrenceLookupComputed input.1 = some tagged) :
    ∃ block : HorizontalRoutedRouteDirectionBlock,
      unitSubdivisionDirections
          (horizontalOccurrenceRibbonCorridorCoreComputed input) =
        horizontalOccurrenceRibbonCorridorDirections input block := by
  rcases horizontalOccurrenceUnitSourceRoute_directionBlock_of_lookup input.1 tagged lookup with
    ⟨block, sourceDirections⟩
  have exactWord := horizontalOccurrenceRibbonCorridor_directions_of_lookup input tagged lookup
  rw [sourceDirections] at exactWord
  exact ⟨block, exactWord⟩

end PeriodicCNFStripReduction
end LeanTrominoes

end
