/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonFanDataEncoding

/-! # Executable variable-fan data for horizontal occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A concrete strip source paired with one normalized routed variable. -/
abbrev HorizontalVariableRibbonFanInput :=
  PeriodicCNF Nat × RoutedVariable

/-- Exact normalized source read by the proof-free finite fan-data builder. -/
def horizontalOccurrenceVariableSourceComputed
    (input : HorizontalVariableRibbonFanInput) : PeriodicCNF RoutedVariable :=
  (horizontalNormalizedRoutedFormulaComputed input.1).erase

/-- Repackage one finite variable-site slot as an executable occurrence-route
query. -/
def horizontalOccurrenceVariableRibbonRouteInput
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    HorizontalOccurrenceRouteInput :=
  (input.1, variableSiteOccurrenceSlot input.2)

/-- Repackage one finite slot as an occurrence-table lookup in the normalized
source. -/
def horizontalOccurrenceVariableRibbonLookupInput
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    (PeriodicCNF RoutedVariable × RoutedVariable) × OccurrenceSlot :=
  ((horizontalOccurrenceVariableSourceComputed input.1, input.1.2),
    variableSiteOccurrenceSlot input.2)

/-- Tagged normalized occurrence occupying one finite variable-site slot. -/
def horizontalOccurrenceVariableRibbonLookupComputed
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    Option (TaggedOccurrence RoutedVariable) :=
  occurrenceAt
    (horizontalOccurrenceVariableRibbonLookupInput input).1.1
    (horizontalOccurrenceVariableRibbonLookupInput input).1.2
    (horizontalOccurrenceVariableRibbonLookupInput input).2

/-- Direction stored for one finite variable-site slot.  Active slots use
the executable occurrence direction; inactive slots use the semantic north
fallback. -/
def horizontalOccurrenceVariableRibbonDirectionSelect
    (input : Bool × AxisDirection) : AxisDirection :=
  if input.1 then input.2 else .north

/-- Direction stored for one finite variable-site slot. -/
def horizontalOccurrenceVariableRibbonDirectionComputed
    (input : HorizontalVariableRibbonFanInput)
    (slot : VariableSiteSlot) : AxisDirection :=
  horizontalOccurrenceVariableRibbonDirectionSelect
    ((horizontalOccurrenceVariableRibbonLookupComputed
      (input, slot)).isSome,
      horizontalOccurrenceSourceVariableDirectionComputed
        (horizontalOccurrenceVariableRibbonRouteInput (input, slot)))

/-- Executable predecessor of the number of active occurrence slots. -/
def horizontalOccurrenceVariableRibbonCountPredComputed
    (input : HorizontalVariableRibbonFanInput) : Fin 3 :=
  if (horizontalOccurrenceVariableRibbonLookupComputed
      (input, .second)).isSome then
    if (horizontalOccurrenceVariableRibbonLookupComputed
        (input, .third)).isSome then
      2
    else
      1
  else
    0

/-- Select the occurrence supplying one fan slot from second- and third-slot
activity plus the requested finite site slot. -/
def horizontalOccurrenceVariableRibbonSiteSlotSelect
    (input : (Bool × Bool) × VariableSiteSlot) : VariableSiteSlot :=
  if input.1.1 then
    if input.1.2 then
      input.2
    else if input.2 = .first then
      .first
    else
      .second
  else
    .first

/-- Occurrence slot supplying one finite variable-fan site. -/
def horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    VariableSiteSlot :=
  horizontalOccurrenceVariableRibbonSiteSlotSelect
    (((horizontalOccurrenceVariableRibbonLookupComputed
        (input.1, .second)).isSome,
      (horizontalOccurrenceVariableRibbonLookupComputed
        (input.1, .third)).isSome), input.2)

/-- Normalized occurrence-table query selected for one finite fan slot. -/
def horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    (PeriodicCNF RoutedVariable × RoutedVariable) × OccurrenceSlot :=
  ((horizontalOccurrenceVariableSourceComputed input.1, input.1.2),
    variableSiteOccurrenceSlot
      (horizontalOccurrenceVariableRibbonSelectedSiteSlotComputed input))

/-- Executable connector kind stored in one finite variable-fan slot. -/
def horizontalOccurrenceVariableRibbonKindComputed
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) :
    VariableConnectorKind :=
  occurrenceConnectorKind
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).1.1
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).1.2
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).2

/-- Executable polarity stored in one finite variable-fan slot. -/
def horizontalOccurrenceVariableRibbonPolarityComputed
    (input : HorizontalVariableRibbonFanInput × VariableSiteSlot) : Bool :=
  occurrencePolarity
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).1.1
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).1.2
    (horizontalOccurrenceVariableRibbonSelectedOccurrenceInputComputed
      input).2

/-- Encoded connector-kind fields of one finite variable fan. -/
def horizontalOccurrenceVariableRibbonKindsCodeComputed
    (input : HorizontalVariableRibbonFanInput) : Fin 3 × Fin 3 × Fin 3 :=
  (variableConnectorKindEquivFin
      (horizontalOccurrenceVariableRibbonKindComputed (input, .first)),
    variableConnectorKindEquivFin
      (horizontalOccurrenceVariableRibbonKindComputed (input, .second)),
    variableConnectorKindEquivFin
      (horizontalOccurrenceVariableRibbonKindComputed (input, .third)))

/-- Encoded polarity fields of one finite variable fan. -/
def horizontalOccurrenceVariableRibbonPolaritiesCodeComputed
    (input : HorizontalVariableRibbonFanInput) : Bool × Bool × Bool :=
  (horizontalOccurrenceVariableRibbonPolarityComputed (input, .first),
    horizontalOccurrenceVariableRibbonPolarityComputed (input, .second),
    horizontalOccurrenceVariableRibbonPolarityComputed (input, .third))

/-- List of the three encoded endpoint-direction fields. -/
def horizontalOccurrenceVariableRibbonDirectionCodesListComputed
    (input : HorizontalVariableRibbonFanInput) : List (Fin 5) :=
  ([.first, .second, .third] : List VariableSiteSlot).map fun slot =>
    axisDirectionEquivFin
      (horizontalOccurrenceVariableRibbonDirectionComputed input slot)

/-- Convert a direction-code list to the three-field fan-code shape. -/
def horizontalOccurrenceVariableRibbonDirectionCodesTriple
    (codes : List (Fin 5)) : Fin 5 × Fin 5 × Fin 5 :=
  (codes.getD 0 0, codes.getD 1 0, codes.getD 2 0)

/-- Encoded endpoint-direction fields of one finite variable fan. -/
def horizontalOccurrenceVariableRibbonDirectionsCodeComputed
    (input : HorizontalVariableRibbonFanInput) : Fin 5 × Fin 5 × Fin 5 :=
  horizontalOccurrenceVariableRibbonDirectionCodesTriple
    (horizontalOccurrenceVariableRibbonDirectionCodesListComputed input)

/-- Canonical finite code of one proof-free variable-fan record. -/
def horizontalOccurrenceVariableRibbonFanCodeComputed
    (input : HorizontalVariableRibbonFanInput) : VariableRibbonFanCode :=
  (horizontalOccurrenceVariableRibbonCountPredComputed input,
    (horizontalOccurrenceVariableRibbonKindsCodeComputed input,
      (horizontalOccurrenceVariableRibbonPolaritiesCodeComputed input,
        horizontalOccurrenceVariableRibbonDirectionsCodeComputed input)))

/-- Complete proof-free finite variable-fan record for one normalized routed
source variable. -/
def horizontalOccurrenceVariableRibbonFanDataComputed
    (input : HorizontalVariableRibbonFanInput) : VariableRibbonFanData :=
  variableRibbonFanDataOfCode
    (horizontalOccurrenceVariableRibbonFanCodeComputed input)

end PeriodicCNFStripReduction
end LeanTrominoes
