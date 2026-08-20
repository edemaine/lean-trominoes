/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableOriginComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteRouteComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes

/-! # Proof-free assembled incidence routes for the horizontal source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PeriodicOrthocrossing
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Input to one translated variable-site incidence prefix. -/
abbrev HorizontalVariableIncidencePrefixInput :=
  ((PeriodicCNF Nat × RoutedVariable) × Triple RoutedVariable) × WireColor

/-- Finite variable-site table query for one typed colored incidence. -/
def horizontalVariableIncidenceLocalRouteInputComputed
    (input : HorizontalVariableIncidencePrefixInput) :
    VariableRibbonFanData × (VariableSiteTriple × WireColor) :=
  (horizontalOccurrenceVariableRibbonFanDataComputed input.1.1,
    (variableSiteTripleOfTyped input.1.2, input.2))

/-- Proof-free finite variable-site route before global translation. -/
def horizontalVariableIncidenceLocalRouteComputed
    (input : HorizontalVariableIncidencePrefixInput) : List Cell :=
  let tableInput := horizontalVariableIncidenceLocalRouteInputComputed input
  variableSiteRouteData tableInput.1 tableInput.2.1 tableInput.2.2

/-- Global origin of the variable module containing one incidence. -/
def horizontalVariableIncidenceOriginComputed
    (input : HorizontalVariableIncidencePrefixInput) : Cell :=
  horizontalThreeDMVariableOriginComputed input.1.1.1 input.1.1.2

/-- A proof-free finite variable-site route translated to its global
macrocell. -/
def horizontalVariableIncidencePrefixComputed
    (input : HorizontalVariableIncidencePrefixInput) : List Cell :=
  translatePolyline
    (horizontalVariableIncidenceOriginComputed input)
    (horizontalVariableIncidenceLocalRouteComputed input)

/-- Input to one complete typed incidence route. -/
abbrev HorizontalTypedIncidenceRouteInput :=
  (PeriodicCNF Nat × Triple RoutedVariable) × WireColor

/-- Constructor data exposed by the ordinary branch of `tripleEquivData`. -/
abbrev HorizontalOrdinaryTypedIncidenceData :=
  ((RoutedVariable × OccurrenceSlot) × VariableOccurrenceVariant) ×
    VariableOccurrenceTriple

/-- Constructor data exposed by the fixed-red branch of `tripleEquivData`. -/
abbrev HorizontalFixedRedTypedIncidenceData :=
  (RoutedVariable × OccurrenceSlot) × FixedRedConnectorTriple

/-- Constructor data exposed by the clause branch of `tripleEquivData`. -/
abbrev HorizontalClauseTypedIncidenceData := Nat × X3CClauseSet

/-- Input to a variable-module incidence, retaining its source occurrence
slot alongside the typed triple. -/
abbrev HorizontalVariableTypedIncidenceRouteInput :=
  (((PeriodicCNF Nat × RoutedVariable) × OccurrenceSlot) ×
    Triple RoutedVariable) × WireColor

/-- Source/atom key assembled from an ordinary constructor branch. -/
def horizontalOrdinaryTypedIncidenceSourceAtomComputed
    (input : HorizontalTypedIncidenceRouteInput ×
      HorizontalOrdinaryTypedIncidenceData) :
    PeriodicCNF Nat × RoutedVariable :=
  (input.1.1.1, input.2.1.1.1)

/-- Source occurrence metadata assembled from an ordinary branch. -/
def horizontalOrdinaryTypedIncidenceMetadataComputed
    (input : HorizontalTypedIncidenceRouteInput ×
      HorizontalOrdinaryTypedIncidenceData) :
    HorizontalOccurrenceRouteInput :=
  (horizontalOrdinaryTypedIncidenceSourceAtomComputed input,
    input.2.1.1.2)

/-- Variable-route input assembled from an ordinary constructor branch. -/
def horizontalOrdinaryTypedIncidenceRouteInputComputed
    (input : HorizontalTypedIncidenceRouteInput ×
      HorizontalOrdinaryTypedIncidenceData) :
    HorizontalVariableTypedIncidenceRouteInput :=
  ((horizontalOrdinaryTypedIncidenceMetadataComputed input, input.1.1.2),
    input.1.2)

/-- Variable-route input assembled from a fixed-red constructor branch. -/
def horizontalFixedRedTypedIncidenceRouteInputComputed
    (input : HorizontalTypedIncidenceRouteInput ×
      HorizontalFixedRedTypedIncidenceData) :
    HorizontalVariableTypedIncidenceRouteInput :=
  ((((input.1.1.1, input.2.1.1), input.2.1.2), input.1.1.2), input.1.2)

/-- Source/atom key retained by a variable incidence. -/
def horizontalVariableTypedIncidenceSourceAtomComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    PeriodicCNF Nat × RoutedVariable :=
  input.1.1.1

/-- Source occurrence metadata retained by a variable incidence. -/
def horizontalVariableTypedIncidenceMetadataComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    HorizontalOccurrenceRouteInput :=
  input.1.1

/-- Normalized erased source used to select the unique routed triple. -/
def horizontalVariableTypedIncidenceNormalizedSourceComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    PeriodicCNF RoutedVariable :=
  (horizontalNormalizedRoutedFormulaComputed
    (horizontalVariableTypedIncidenceSourceAtomComputed input).1).erase

/-- Prefix query extracted from a variable-module incidence. -/
def horizontalVariableRoutePrefixQueryComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    HorizontalVariableIncidencePrefixInput :=
  ((horizontalVariableTypedIncidenceSourceAtomComputed input,
    input.1.2), input.2)

/-- Generic routed-triple query extracted from a variable incidence. -/
def horizontalRoutedOccurrenceTripleInputComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    ((PeriodicCNF RoutedVariable × RoutedVariable) × OccurrenceSlot) ×
      WireColor :=
  ((((horizontalVariableTypedIncidenceNormalizedSourceComputed input),
      (horizontalVariableTypedIncidenceSourceAtomComputed input).2),
    (horizontalVariableTypedIncidenceMetadataComputed input).2), input.2)

/-- Expected routed triple of a variable-module colored incidence. -/
def horizontalRoutedOccurrenceTripleQueryComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    Triple RoutedVariable :=
  routedOccurrenceTriple
    (horizontalRoutedOccurrenceTripleInputComputed input).1.1.1
    (horizontalRoutedOccurrenceTripleInputComputed input).1.1.2
    (horizontalRoutedOccurrenceTripleInputComputed input).1.2
    (horizontalRoutedOccurrenceTripleInputComputed input).2

/-- Complete occurrence-route query extracted from a variable incidence. -/
def horizontalVariableOccurrenceRouteQueryComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) :
    HorizontalOccurrenceColoredRouteInput :=
  (horizontalVariableTypedIncidenceMetadataComputed input, input.2)

/-- Complete variable-module incidence route, extending exactly the unique
routed local prefix by its source-to-clause route. -/
def horizontalVariableTypedIncidenceRouteComputed
    (input : HorizontalVariableTypedIncidenceRouteInput) : List Cell :=
  let prefixRoute := horizontalVariableIncidencePrefixComputed
    (horizontalVariableRoutePrefixQueryComputed input)
  if input.1.2 = horizontalRoutedOccurrenceTripleQueryComputed input then
    joinAtEndpoint prefixRoute
      (horizontalOccurrenceCoordinatedRouteComputed
        (horizontalVariableOccurrenceRouteQueryComputed input))
  else
    prefixRoute

/-- Input to one translated clause-core incidence route. -/
abbrev HorizontalClauseIncidenceRouteInput :=
  ((PeriodicCNF Nat × Nat) × X3CClauseSet) × WireColor

/-- Clause-route input assembled from a clause constructor branch. -/
def horizontalClauseTypedIncidenceRouteInputComputed
    (input : HorizontalTypedIncidenceRouteInput ×
      HorizontalClauseTypedIncidenceData) :
    HorizontalClauseIncidenceRouteInput :=
  (((input.1.1.1, input.2.1), input.2.2), input.1.2)

/-- Proof-free translated route of one clause-core incidence. -/
def horizontalClauseIncidenceRouteComputed
    (input : HorizontalClauseIncidenceRouteInput) : List Cell :=
  translatePolyline
    (horizontalThreeDMClauseOriginComputed input.1.1.1 input.1.1.2)
    (X3CClauseOrthogonal.route input.1.2 input.2)

/-- Complete proof-free route of one typed colored incidence.  The unique
routed incidence in each variable module is extended by its coordinated
source-to-clause route; all other variable incidences retain their local
prefix. -/
def horizontalTypedIncidenceRouteComputed
    (input : HorizontalTypedIncidenceRouteInput) : List Cell :=
  let source := input.1.1
  let triple := input.1.2
  let color := input.2
  match triple with
  | .ordinary atom slot variant localTriple =>
      let typed : Triple RoutedVariable :=
        .ordinary atom slot variant localTriple
      horizontalVariableTypedIncidenceRouteComputed
        ((((source, atom), slot), typed), color)
  | .fixedRed atom slot localTriple =>
      let typed : Triple RoutedVariable := .fixedRed atom slot localTriple
      horizontalVariableTypedIncidenceRouteComputed
        ((((source, atom), slot), typed), color)
  | .clause clauseIndex set =>
      horizontalClauseIncidenceRouteComputed
        (((source, clauseIndex), set), color)

end PeriodicCNFStripReduction
end LeanTrominoes
