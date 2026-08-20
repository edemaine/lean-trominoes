/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceRouteLookup
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidenceFirstDirection
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteTripleLookupSemanticBridge

/-! # Variable-incidence directions in the horizontal normalization input -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A successful stable triple lookup supplies membership in the semantic
typed-triple list. -/
theorem horizontalAssembledRouteTriple?Computed_mem_semantic
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (triple : Triple RoutedVariable)
    (lookup : horizontalAssembledRouteTriple?Computed (source, tag) =
      some triple) :
    triple ∈ triples
      (horizontalSemanticNormalizedRibbonSource source).erase := by
  have semanticLookup :
      (horizontalSemanticThreeDMTypedTriples source)[tag.tripleIndex]? =
        some triple := by
    rw [← horizontalAssembledRouteTriple?Computed_eq_semantic]
    exact lookup
  have parts := List.getElem?_eq_some_iff.mp semanticLookup
  have listMember :
      triple ∈ horizontalSemanticThreeDMTypedTriples source := by
    rw [← parts.2]
    exact List.getElem_mem parts.1
  exact listMember

/-- A successful stable lookup evaluates the stored route at precisely the
selected typed triple. -/
theorem horizontalAssembledRouteAtTagComputed_eq_typedRoute
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (triple : Triple RoutedVariable)
    (lookup : horizontalAssembledRouteTriple?Computed (source, tag) =
      some triple) :
    horizontalAssembledRouteAtTagComputed (source, tag) =
      horizontalTypedIncidenceRouteComputed
        ((source, triple), tag.color) := by
  unfold horizontalAssembledRouteAtTagComputed typedRouteFromOptionData
  rw [lookup]

@[simp] theorem horizontalTypedIncidenceRouteComputed_ordinary
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (color : WireColor) :
    horizontalTypedIncidenceRouteComputed
        ((source, Triple.ordinary atom slot variant localTriple), color) =
      horizontalVariableTypedIncidenceRouteComputed
        ((((source, atom), slot),
          Triple.ordinary atom slot variant localTriple), color) := by
  rfl

@[simp] theorem horizontalTypedIncidenceRouteComputed_fixedRed
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (color : WireColor) :
    horizontalTypedIncidenceRouteComputed
        ((source, Triple.fixedRed atom slot localTriple), color) =
      horizontalVariableTypedIncidenceRouteComputed
        ((((source, atom), slot),
          Triple.fixedRed atom slot localTriple), color) := by
  rfl

/-- A selected ordinary incidence in the normalization input has the first
direction of its finite local variable-site table entry. -/
theorem horizontalNormalizationOrdinaryIncidenceFirstDirectionComputed
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags)
    (tripleEq :
      horizontalAssembledRouteTriple?Computed (source, tag) =
        some (.ordinary atom slot variant localTriple)) :
    AxisDirection.polylineFirstDirection
        (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
          (horizontalNormalizationInputComputed source) tag) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidenceLocalRouteComputed
          (((source, atom),
            Triple.ordinary atom slot variant localTriple), tag.color)) := by
  rw [horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    source tag tagMember]
  rw [horizontalAssembledRouteAtTagComputed_eq_typedRoute
    source tag _ tripleEq]
  rw [horizontalTypedIncidenceRouteComputed_ordinary]
  exact horizontalOrdinaryVariableTypedIncidenceRouteComputed_firstDirection
    source atom slot variant localTriple
      (horizontalAssembledRouteTriple?Computed_mem_semantic
        source tag _ tripleEq)
      tag.color

/-- A selected fixed-red incidence in the normalization input has the first
direction of its finite local variable-site table entry. -/
theorem horizontalNormalizationFixedRedIncidenceFirstDirectionComputed
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags)
    (tripleEq :
      horizontalAssembledRouteTriple?Computed (source, tag) =
        some (.fixedRed atom slot localTriple)) :
    AxisDirection.polylineFirstDirection
        (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
          (horizontalNormalizationInputComputed source) tag) =
      AxisDirection.polylineFirstDirection
        (horizontalVariableIncidenceLocalRouteComputed
          (((source, atom), Triple.fixedRed atom slot localTriple),
            tag.color)) := by
  rw [horizontalNormalizationIncidenceRouteComputed_eq_routeAtTag
    source tag tagMember]
  rw [horizontalAssembledRouteAtTagComputed_eq_typedRoute
    source tag _ tripleEq]
  rw [horizontalTypedIncidenceRouteComputed_fixedRed]
  exact horizontalFixedRedVariableTypedIncidenceRouteComputed_firstDirection
    source atom slot localTriple
      (horizontalAssembledRouteTriple?Computed_mem_semantic
        source tag _ tripleEq)
      tag.color

end PeriodicCNFStripReduction
end LeanTrominoes
