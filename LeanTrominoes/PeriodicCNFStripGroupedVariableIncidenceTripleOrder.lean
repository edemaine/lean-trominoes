/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumeration

/-! # Typed triple order of grouped variable-incidence prefixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- Once the selected connector kind agrees, the finite grouped triple block
is exactly the typed occurrence block with its periodic atom name erased. -/
theorem groupedVariableIncidenceTriples_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (kindEq : fan.kind (occurrenceVariableSiteSlot slot) =
      occurrenceConnectorKind source atom slot) :
    groupedVariableIncidenceTriples
        (fan, groupedVariableFanGenericSlot slot) =
      (occurrenceTriples source atom slot).map variableSiteTripleOfTyped := by
  unfold groupedVariableIncidenceTriples occurrenceTriples
  simp only [groupedVariableFanSiteSlot_genericSlot]
  rw [kindEq]
  cases occurrenceConnectorKind source atom slot <;>
    simp [List.map_map, Function.comp_def, variableSiteTripleOfTyped]

/-- The grouped finite prefix bodies use exactly typed triple-major,
red/green/blue-minor order after erasing periodic atom names. -/
theorem groupedVariableIncidencePrefixBodies_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (fan : VariableRibbonFanData)
    (kindEq : fan.kind (occurrenceVariableSiteSlot slot) =
      occurrenceConnectorKind source atom slot) :
    (groupedVariableIncidencePrefixQueryBlock
        (fan, groupedVariableFanGenericSlot slot)).map
          HorizontalFiniteIncidenceDirectionQuery.directions =
      (occurrenceTriples source atom slot).flatMap fun triple =>
        ([.red, .green, .blue] : List WireColor).map fun color =>
          HorizontalFiniteIncidenceDirectionQuery.directions
            (.variable fan (variableSiteTripleOfTyped triple) color) := by
  unfold groupedVariableIncidencePrefixQueryBlock
  rw [groupedVariableIncidenceTriples_eq_typed
    source atom slot fan kindEq]
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro triple _tripleMember
  simp

end LeanTrominoes.PeriodicCNFStripReduction

end
