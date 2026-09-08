/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripTypedIncidenceElementCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeSelectorSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceTripleOrder

/-! # Finite variable selectors name the actual typed references -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

private theorem nextCycleSelector_code {Variable : Type*}
    (key : Variable × OccurrenceSlot → Nat) (atom : Variable)
    (slot nextSlot : OccurrenceSlot) (parent : Nat) :
    variableIncidenceElementCode
        (if nextSlot = slot then
          variableIncidenceElementSelector .currentOccurrence 0
        else variableIncidenceElementSelector .nextOccurrence 0)
        (key (atom, slot)) (key (atom, nextSlot)) parent =
      key (atom, nextSlot) * 32 := by
  by_cases same : nextSlot = slot
  · simp [same, variableIncidenceElementCode_current, directSourceFinalElementCodeStride]
  · simp [same, variableIncidenceElementCode_next, directSourceFinalElementCodeStride]

/-- A selector's current, successor, and parent bases refer to exactly the
colored typed element of the corresponding occurrence triple. -/
theorem groupedVariableIncidenceElementSelector_code_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (fan : VariableRibbonFanData)
    (fanCount : fan.count = sourceVariableSiteCount source atom)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) = occurrenceConnectorKind source atom slot)
    (fanPolarity : fan.polarity (occurrenceVariableSiteSlot slot) = occurrencePolarity source atom slot)
    (key : Variable × OccurrenceSlot → Nat) (triple : Triple Variable)
    (member : triple ∈ occurrenceTriples source atom slot) (color : WireColor) :
    variableIncidenceElementCode
        (groupedVariableIncidenceElementSelector (fan, groupedVariableFanGenericSlot slot)
          (variableSiteTripleOfTyped triple) color)
        (key (atom, slot)) (key (atom, nextUsedSlot source atom slot))
        (occurrenceClauseIndex source atom slot) =
      TypedElementCode.reference key (tripleReferences source triple) color := by
  have successor := occurrenceVariableSiteSlot_nextUsedSlot source atom atomMember slot slotMember
  cases terminalEq : terminalGroupOfLiteralIndex (occurrenceLiteralIndex source atom slot) <;>
    simp only [occurrenceTriples, occurrenceConnectorKind, connectorKindOfLiteralIndex,
      terminalEq, variableConnectorKindForTerminal] at member
  all_goals
    obtain ⟨localTriple, _, rfl⟩ := List.mem_map.mp member
    cases localTriple <;> cases color <;>
      cases polarityEq : occurrencePolarity source atom slot <;>
      simp [groupedVariableIncidenceElementSelector, groupedVariableFanSiteSlot_genericSlot,
        variableSiteTripleOfTyped, variableSiteReferenceBase, ordinaryVariableSiteElement,
        fixedRedVariableSiteElement, VariableOccurrence.reference, VariableOccurrenceTriple.references,
        FixedRedConnector.reference, FixedRedConnectorTriple.references,
        fanCount, fanKind, fanPolarity, ← successor, polarityEq, nextCycleSelector_code,
        variableIncidenceElementCode_current,
        variableIncidenceElementCode_parent, variableIncidenceClauseTerminalTag,
        directSourceFinalElementCodeStride, occurrenceConnectorKind, connectorKindOfLiteralIndex,
        terminalEq, variableConnectorKindForTerminal, TypedElementCode.reference,
        TypedElementCode.red, TypedElementCode.green, TypedElementCode.blue,
        tripleReferences, ordinaryTripleReferences, fixedRedTripleReferences,
        ordinaryRedElement, ordinaryGreenElement, ordinaryBlueElement,
        fixedRedRedElement, fixedRedGreenElement, fixedRedBlueElement,
        firstCycleLinkSlot, secondCycleLinkSlot,
        redClauseTerminal, greenClauseTerminal, blueClauseTerminal]

/-- Exact finite selector interpretation lifts to the full local incidence
block without changing typed-triple or red/green/blue order. -/
theorem groupedVariableIncidenceElementCodeBlock_eq_typed
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable)
    (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (fan : VariableRibbonFanData)
    (fanCount : fan.count = sourceVariableSiteCount source atom)
    (fanKind : fan.kind (occurrenceVariableSiteSlot slot) = occurrenceConnectorKind source atom slot)
    (fanPolarity : fan.polarity (occurrenceVariableSiteSlot slot) = occurrencePolarity source atom slot)
    (key : Variable × OccurrenceSlot → Nat) :
    groupedVariableIncidenceElementCodeBlock (fan, groupedVariableFanGenericSlot slot)
        (key (atom, slot)) (key (atom, nextUsedSlot source atom slot))
        (occurrenceClauseIndex source atom slot) =
      (occurrenceTriples source atom slot).flatMap (fun triple => incidenceColors.map fun color =>
        TypedElementCode.reference key (tripleReferences source triple) color) := by
  unfold groupedVariableIncidenceElementCodeBlock groupedVariableIncidenceElementSelectorBlock
  rw [groupedVariableIncidenceTriples_eq_typed source atom slot fan fanKind,
    List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro triple member
  change (incidenceColors.map (fun color => variableIncidenceElementCode
    (groupedVariableIncidenceElementSelector (fan, groupedVariableFanGenericSlot slot)
      (variableSiteTripleOfTyped triple) color)
    (key (atom, slot)) (key (atom, nextUsedSlot source atom slot))
    (occurrenceClauseIndex source atom slot))) = _
  apply List.map_congr_left
  intro color _
  exact groupedVariableIncidenceElementSelector_code_eq_typed source atom atomMember slot slotMember
    fan fanCount fanKind fanPolarity key triple member color

end LeanTrominoes.PeriodicCNFStripReduction

end
