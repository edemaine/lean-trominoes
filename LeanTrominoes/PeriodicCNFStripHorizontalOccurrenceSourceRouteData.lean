/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRoutedFormulaComputability
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridors

/-! # Proof-free occurrence source routes for the horizontal reduction -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRoutedPlacementVariableDecidableEq

/-- An occurrence slot in the final normalized exact-one source. -/
abbrev HorizontalOccurrenceRouteInput :=
  (PeriodicCNF Nat × RoutedVariable) × OccurrenceSlot

/-- The same query after a concrete tagged occurrence has been found. -/
abbrev HorizontalOccurrenceRouteSomeInput :=
  HorizontalOccurrenceRouteInput × TaggedOccurrence RoutedVariable

/-- The normalized source clause named by a tagged occurrence. -/
def horizontalOccurrenceClauseComputed
    (input : HorizontalOccurrenceRouteSomeInput) :
    PeriodicClause RoutedVariable :=
  (((horizontalNormalizedRoutedFormulaComputed input.1.1.1).clauses[
      input.2.2.1]?).map PositionedPeriodicClause.literals).getD []

/-- Physical rebasing translation from the stored clause-to-variable route
to the variable-to-clause convention used by the ribbon construction. -/
def horizontalOccurrenceTranslationComputed
    (input : HorizontalOccurrenceRouteSomeInput) : Cell :=
  Cell.scale (horizontalPaddedRoutedPeriodComputed input.1.1.1)
    (Cell.sub
      (PeriodicCNF.clauseAnchor
        (horizontalOccurrenceClauseComputed input))
      input.2.1.offset)

/-- The doubled stored incidence route, reversed into the ribbon direction. -/
def horizontalOccurrenceRouteQueryInput
    (input : HorizontalOccurrenceRouteSomeInput) :
    (PeriodicCNF Nat × Nat) × Nat :=
  ((input.1.1.1, input.2.2.1), input.2.2.2)

/-- The stored route selected by the tagged occurrence indices. -/
def horizontalOccurrenceStoredRouteComputed
    (input : HorizontalOccurrenceRouteSomeInput) : List Cell :=
  horizontalRoutedRoutesComputed
    (horizontalOccurrenceRouteQueryInput input).1.1
    (horizontalOccurrenceRouteQueryInput input).1.2
    (horizontalOccurrenceRouteQueryInput input).2

/-- The stored incidence route after the padding scale. -/
def horizontalOccurrenceScaledRouteComputed
    (input : HorizontalOccurrenceRouteSomeInput) : List Cell :=
  scalePolyline 2 (horizontalOccurrenceStoredRouteComputed input)

/-- The doubled stored incidence route, reversed into the ribbon direction. -/
def horizontalOccurrenceReversedRouteComputed
    (input : HorizontalOccurrenceRouteSomeInput) : List Cell :=
  (horizontalOccurrenceScaledRouteComputed input).reverse

/-- Complete proof-free rebased source route for a found occurrence. -/
def horizontalOccurrenceSourceRouteSomeComputed
    (input : HorizontalOccurrenceRouteSomeInput) : List Cell :=
  translatePolyline
    (horizontalOccurrenceTranslationComputed input)
    (horizontalOccurrenceReversedRouteComputed input)

/-- Repackage one occurrence slot as the generic occurrence-table query. -/
def horizontalOccurrenceLookupInput
    (input : HorizontalOccurrenceRouteInput) :
    (PeriodicCNF RoutedVariable × RoutedVariable) × OccurrenceSlot :=
  (((horizontalNormalizedRoutedFormulaComputed input.1.1).erase,
    input.1.2), input.2)

/-- Tagged occurrence selected by the normalized exact-one source. -/
def horizontalOccurrenceLookupComputed
    (input : HorizontalOccurrenceRouteInput) :
    Option (TaggedOccurrence RoutedVariable) :=
  occurrenceAt
    (horizontalOccurrenceLookupInput input).1.1
    (horizontalOccurrenceLookupInput input).1.2
    (horizontalOccurrenceLookupInput input).2

/-- Total proof-free rebased source route.  An inactive slot uses the empty
fallback; every assembled routed incidence supplies an active slot. -/
def horizontalOccurrenceSourceRouteComputed
    (input : HorizontalOccurrenceRouteInput) : List Cell :=
  match horizontalOccurrenceLookupComputed input with
  | none => []
  | some tagged =>
      horizontalOccurrenceSourceRouteSomeComputed (input, tagged)

end PeriodicCNFStripReduction
end LeanTrominoes
