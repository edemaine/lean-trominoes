/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOrdinaryIncidencePrefixSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidenceQuerySemanticBridge

/-! # Semantic bridge for complete horizontal ordinary incidences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalVariableTypedIncidenceRouteComputed_eq_assembledOrdinary
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member : Triple.ordinary atom slot variant localTriple ∈
      @triples RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalVariableTypedIncidenceRouteComputed
        ((((source, atom), slot),
          Triple.ordinary atom slot variant localTriple), color) =
      @assembledTypedIncidenceRoute
        RoutedVariable horizontalRibbonRoutedVariableDecidableEq
        (horizontalSemanticNormalizedRibbonSource source).erase
        (coordinatedSourceRibbonThreeStrandRouting
          (horizontalSemanticNormalizedRibbonReadyPresentation source)
          width compatible)
        (⟨Triple.ordinary atom slot variant localTriple, member⟩ :
          {triple : Triple RoutedVariable //
            triple ∈
              @triples RoutedVariable
                horizontalRibbonRoutedVariableDecidableEq
                (horizontalSemanticNormalizedRibbonSource source).erase})
        color := by
  let typed : Triple RoutedVariable :=
    .ordinary atom slot variant localTriple
  let location := ordinaryTriple_location
    (horizontalSemanticNormalizedRibbonSource source).erase
    atom slot variant localTriple member
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨location.1, location.2.1⟩⟩
  have prefixEq :=
    horizontalVariableIncidencePrefixComputed_eq_assembledOrdinary
      source width compatible atom slot variant localTriple member color
  have routed :=
    horizontalRoutedOccurrenceTripleQueryComputed_eq_semantic
      source entry typed color
  have occurrence :=
    horizontalVariableOccurrenceRouteComputed_eq_routing
      source width compatible entry typed color
  simp only [entry, typed] at routed occurrence
  unfold horizontalVariableTypedIncidenceRouteComputed
    horizontalVariableRoutePrefixQueryComputed
    horizontalVariableTypedIncidenceSourceAtomComputed
    assembledTypedIncidenceRoute
  rw [routed]
  by_cases isRouted :
      Triple.ordinary atom slot variant localTriple =
        routedOccurrenceTriple
          (horizontalSemanticNormalizedRibbonSource source).erase
          atom slot color
  · simp only [if_pos isRouted, dif_pos isRouted]
    rw [prefixEq, occurrence]
    congr 2
  · simp only [if_neg isRouted, dif_neg isRouted]
    exact prefixEq

end PeriodicCNFStripReduction
end LeanTrominoes
