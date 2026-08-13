/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositions
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Global incidence routes for the planar 3DM assembly

This file emits one route for each encoded RGB incidence.  Clause-core
incidences are translated copies of the checked clause drawing.  A variable
incidence starts with its route in the checked complete variable-site
drawing; the uniquely classified routed incidence is then joined to its
certified three-strand corridor.

The construction is indexed by attached typed triples, so all membership
proofs needed to select the correct finite variable site remain internal.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- Membership of an ordinary typed triple identifies its active variable
and occurrence block. -/
theorem ordinaryTriple_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      Triple.ordinary atom slot variant localTriple ∈
        occurrenceTriples source atom slot := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · rw [variableTriples_eq_occurrenceEntries_flatMap] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨entry, entryMember, blockMember⟩
    rcases entry with ⟨entryAtom, entrySlot⟩
    have entryParts :=
      (mem_occurrenceEntries_iff
        source entryAtom entrySlot).mp entryMember
    cases kindEq :
        occurrenceConnectorKind source entryAtom entrySlot <;>
      simp [occurrenceTriples, kindEq, allFixedRedTriples,
        allOrdinaryTriples] at blockMember
    all_goals
      rcases blockMember with
        ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl, rfl⟩
    all_goals
      simp_all [occurrenceTriples, allOrdinaryTriples]
  · simp [clauseTriples, allClauseSets] at clauseMember

/-- Membership of a fixed-red typed triple identifies its active variable
and occurrence block. -/
theorem fixedRedTriple_location
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source) :
    atom ∈ occurringVariables source ∧
      slot ∈ usedSlots source atom ∧
      Triple.fixedRed atom slot localTriple ∈
        occurrenceTriples source atom slot := by
  rw [triples, List.mem_append] at member
  rcases member with variableMember | clauseMember
  · rw [variableTriples_eq_occurrenceEntries_flatMap] at variableMember
    rcases List.mem_flatMap.mp variableMember with
      ⟨entry, entryMember, blockMember⟩
    rcases entry with ⟨entryAtom, entrySlot⟩
    have entryParts :=
      (mem_occurrenceEntries_iff
        source entryAtom entrySlot).mp entryMember
    cases kindEq :
        occurrenceConnectorKind source entryAtom entrySlot <;>
      simp [occurrenceTriples, kindEq, allFixedRedTriples,
        allOrdinaryTriples] at blockMember
    all_goals
      rcases blockMember with
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩
    all_goals
      simp_all [occurrenceTriples, allFixedRedTriples]
  · simp [clauseTriples, allClauseSets] at clauseMember

/-- An ordinary variable incidence route inside its complete finite site,
translated to the global variable origin. -/
def assembledOrdinaryPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) : List Cell :=
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  PeriodicOrthocrossing.translatePolyline
    (routing.variableOrigin atom)
    (typedVariableSiteRoute source atom location.1 slot location.2.1
      (.ordinary atom slot variant localTriple) location.2.2
      color)

/-- A fixed-red variable incidence route inside its complete finite site,
translated to the global variable origin. -/
def assembledFixedRedPrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) : List Cell :=
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  PeriodicOrthocrossing.translatePolyline
    (routing.variableOrigin atom)
    (typedVariableSiteRoute source atom location.1 slot location.2.1
      (.fixedRed atom slot localTriple) location.2.2 color)

/-- The active finite ordinary triple position agrees with the direct
relative-coordinate formula used by the global vertex list. -/
theorem activeOrdinaryTriple_position
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (tripleMember :
      Triple.ordinary atom slot variant localTriple ∈
        occurrenceTriples source atom slot) :
    (sourceVariableSiteDrawing source atom).triplePosition
        (activeVariableSiteTriple source atom atomMember slot slotMember
          (.ordinary atom slot variant localTriple) tripleMember) =
      placeVariableModulePoint
        (occurrenceVariableSiteSlot slot)
        (orientedTripleLocalPosition source
          (.ordinary atom slot variant localTriple)) := by
  have polarityAt :=
    sourceVariableSitePolarity_active source atom atomMember
      slot slotMember
  simp [sourceVariableSiteDrawing, variableSiteDrawing,
    variableSiteTriplePosition, activeVariableSiteTriple,
    variableSiteTripleOfTyped, polarityAt,
    orientedTripleLocalPosition]

/-- The active finite fixed-red triple position has the analogous direct
relative-coordinate formula. -/
theorem activeFixedRedTriple_position
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (localTriple : FixedRedConnectorTriple)
    (tripleMember :
      Triple.fixedRed atom slot localTriple ∈
        occurrenceTriples source atom slot) :
    (sourceVariableSiteDrawing source atom).triplePosition
        (activeVariableSiteTriple source atom atomMember slot slotMember
          (.fixedRed atom slot localTriple) tripleMember) =
      placeVariableModulePoint
        (occurrenceVariableSiteSlot slot)
        (orientedTripleLocalPosition source
          (.fixedRed atom slot localTriple)) := by
  have polarityAt :=
    sourceVariableSitePolarity_active source atom atomMember
      slot slotMember
  simp [sourceVariableSiteDrawing, variableSiteDrawing,
    variableSiteTriplePosition, activeVariableSiteTriple,
    variableSiteTripleOfTyped, polarityAt,
    orientedTripleLocalPosition]

/-- A translated ordinary prefix starts at its globally assembled typed
triple position. -/
theorem assembledOrdinaryPrefix_head
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) :
    (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color).head? =
      some (assembledTriplePosition routing
        (.ordinary atom slot variant localTriple)) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color
  simp only [assembledOrdinaryPrefix,
    PeriodicOrthocrossing.translatePolyline, List.head?_map,
    endpoints.1, Option.map_some]
  congr 2
  exact activeOrdinaryTriple_position source atom location.1 slot
    location.2.1 variant localTriple location.2.2

/-- A translated fixed-red prefix starts at its globally assembled typed
triple position. -/
theorem assembledFixedRedPrefix_head
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) :
    (assembledFixedRedPrefix routing atom slot localTriple
        member color).head? =
      some (assembledTriplePosition routing
        (.fixedRed atom slot localTriple)) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color
  simp only [assembledFixedRedPrefix,
    PeriodicOrthocrossing.translatePolyline, List.head?_map,
    endpoints.1, Option.map_some]
  congr 2
  exact activeFixedRedTriple_position source atom location.1 slot
    location.2.1 localTriple location.2.2

/-- A clause-core incidence translated to its global clause neighborhood. -/
def assembledClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) : List Cell :=
  PeriodicOrthocrossing.translatePolyline
    (routing.clauseOrigin clauseIndex)
    (orientedIncidenceLocalRoute source (.clause clauseIndex set) color)

/-- Global target of one typed colored reference, including its semantic
lattice offset scaled by the physical period. -/
def assembledTypedReferenceTargetPosition
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : Triple Variable) : WireColor → Cell
  | .red =>
      Cell.add
        (assembledRedElementPosition routing
          (tripleReferences source triple).red.atom)
        (routing.periodTranslation
          (tripleReferences source triple).red.offset)
  | .green =>
      Cell.add
        (assembledGreenElementPosition routing
          (tripleReferences source triple).green.atom)
        (routing.periodTranslation
          (tripleReferences source triple).green.offset)
  | .blue =>
      Cell.add
        (assembledBlueElementPosition routing
          (tripleReferences source triple).blue.atom)
        (routing.periodTranslation
          (tripleReferences source triple).blue.offset)

/-- The certified corridor target is exactly the global target of the
routed typed 3DM reference. -/
theorem routedClauseTargetPosition_eq_typedReference
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    routedClauseTargetPosition source routing.period
        routing.clauseOrigin entry color =
      assembledTypedReferenceTargetPosition routing
        (routedOccurrenceTriple
          source entry.1.1 entry.1.2 color) color := by
  cases color with
  | red =>
      simp only [assembledTypedReferenceTargetPosition]
      rw [routedOccurrenceTriple_red_reference]
      apply Prod.ext <;>
        simp [routedClauseTargetPosition, routedClausePortPosition,
        assembledRedElementPosition,
        redClauseTerminal,
        ThreeStrandRouting.periodTranslation, Cell.add, Cell.scale]
  | green =>
      simp only [assembledTypedReferenceTargetPosition]
      rw [routedOccurrenceTriple_green_reference]
      apply Prod.ext <;>
        simp [routedClauseTargetPosition, routedClausePortPosition,
        assembledGreenElementPosition,
        greenClauseTerminal,
        ThreeStrandRouting.periodTranslation, Cell.add, Cell.scale]
  | blue =>
      simp only [assembledTypedReferenceTargetPosition]
      rw [routedOccurrenceTriple_blue_reference]
      apply Prod.ext <;>
        simp [routedClauseTargetPosition, routedClausePortPosition,
        assembledBlueElementPosition,
        blueClauseTerminal,
        ThreeStrandRouting.periodTranslation, Cell.add, Cell.scale]

/-- A clause template's advertised local port becomes exactly the global
target of its zero-offset typed reference. -/
theorem assembledClausePort_eq_typedReference
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    Cell.add (routing.clauseOrigin clauseIndex)
        (orientedIncidencePortPosition
          source (.clause clauseIndex set) color) =
      assembledTypedReferenceTargetPosition routing
        (.clause clauseIndex set) color := by
  cases color <;> cases set <;>
    apply Prod.ext <;>
    simp [orientedIncidencePortPosition,
      assembledTypedReferenceTargetPosition,
      tripleReferences, clauseTripleReferences,
      assembledRedElementPosition,
      assembledGreenElementPosition,
      assembledBlueElementPosition,
      ThreeStrandRouting.periodTranslation,
      clauseRedElement, clauseGreenElement, clauseBlueElement,
      X3CClauseOrthogonal.reference,
      X3CClauseSet.coloredReferences,
      X3CClauseOrthogonal.elementPosition,
      terminalElementForColor,
      redClauseElementLocalPosition,
      greenClauseElementLocalPosition,
      blueClauseElementLocalPosition,
      Cell.add, Cell.scale]

/-- Every translated clause-core route has the exact global typed
endpoints. -/
theorem assembledClauseRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    (assembledClauseRoute routing clauseIndex set color).head? =
        some (assembledTriplePosition routing
          (.clause clauseIndex set)) ∧
      (assembledClauseRoute routing clauseIndex set color).getLast? =
        some (assembledTypedReferenceTargetPosition routing
          (.clause clauseIndex set) color) := by
  have endpoints :=
    orientedIncidenceLocalRoute_endpoints source
      (.clause clauseIndex set) color
  constructor
  · simpa [assembledClauseRoute,
      PeriodicOrthocrossing.translatePolyline,
      assembledTriplePosition] using congrArg
        (Option.map (Cell.add (routing.clauseOrigin clauseIndex)))
        endpoints.1
  · have translated :=
      congrArg
        (Option.map (Cell.add (routing.clauseOrigin clauseIndex)))
        endpoints.2
    simpa [assembledClauseRoute,
      PeriodicOrthocrossing.translatePolyline,
      assembledClausePort_eq_typedReference] using translated

/-- A local ordinary variable incidence's finite target is exactly its
globally assembled typed element vertex. -/
theorem activeOrdinaryReference_position_local
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (tripleMember :
      Triple.ordinary atom slot variant localTriple ∈
        occurrenceTriples source atom slot)
    (color : WireColor)
    (localIncidence :
      IncidenceIsLocal source color
        (.ordinary atom slot variant localTriple)) :
    let active :=
      activeVariableSiteTriple source atom atomMember slot slotMember
        (.ordinary atom slot variant localTriple) tripleMember
    Cell.add (routing.variableOrigin atom)
        ((sourceVariableSiteDrawing source atom).elementPosition
          ((sourceVariableSiteDrawing source atom).reference
            active color)) =
      assembledTypedReferenceTargetPosition routing
        (.ordinary atom slot variant localTriple) color := by
  have polarityAt :=
    sourceVariableSitePolarity_active source atom atomMember
      slot slotMember
  have successorAt :=
    occurrenceVariableSiteSlot_nextUsedSlot source atom atomMember
      slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceTriples, kindEq, allFixedRedTriples,
      allOrdinaryTriples] at tripleMember
  all_goals
    rcases tripleMember with
      ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    cases polarityEq : occurrencePolarity source atom slot <;>
      cases color <;>
      simp_all [IncidenceIsLocal,
        tripleSite, redElementSite, greenElementSite, blueElementSite,
        redClauseTerminal, greenClauseTerminal, blueClauseTerminal,
        sourceVariableSiteDrawing, variableSiteDrawing,
        variableSiteReference, variableSiteReferenceBase,
        variableSiteElementPosition, activeVariableSiteTriple,
        variableSiteTripleOfTyped, ordinaryVariableSiteElement,
        VariableOccurrence.reference,
        VariableOccurrenceTriple.references,
        assembledTypedReferenceTargetPosition,
        tripleReferences, ordinaryTripleReferences,
        ordinaryRedElement, ordinaryGreenElement, ordinaryBlueElement,
        firstCycleLinkSlot, secondCycleLinkSlot,
        assembledRedElementPosition,
        assembledGreenElementPosition,
        assembledBlueElementPosition,
        ordinaryInternalSitePosition, ordinaryVariantAt,
        ordinaryInternalLocalElement,
        ThreeStrandRouting.periodTranslation,
        occurrenceVariableSiteSlot, Cell.add, Cell.scale]

/-- A local fixed-red variable incidence's finite target is exactly its
globally assembled typed element vertex. -/
theorem activeFixedRedReference_position_local
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (localTriple : FixedRedConnectorTriple)
    (tripleMember :
      Triple.fixedRed atom slot localTriple ∈
        occurrenceTriples source atom slot)
    (color : WireColor)
    (localIncidence :
      IncidenceIsLocal source color
        (.fixedRed atom slot localTriple)) :
    let active :=
      activeVariableSiteTriple source atom atomMember slot slotMember
        (.fixedRed atom slot localTriple) tripleMember
    Cell.add (routing.variableOrigin atom)
        ((sourceVariableSiteDrawing source atom).elementPosition
          ((sourceVariableSiteDrawing source atom).reference
            active color)) =
      assembledTypedReferenceTargetPosition routing
        (.fixedRed atom slot localTriple) color := by
  have polarityAt :=
    sourceVariableSitePolarity_active source atom atomMember
      slot slotMember
  have successorAt :=
    occurrenceVariableSiteSlot_nextUsedSlot source atom atomMember
      slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceTriples, kindEq, allFixedRedTriples,
      allOrdinaryTriples] at tripleMember
  all_goals
    rcases tripleMember with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩
  all_goals
    cases polarityEq : occurrencePolarity source atom slot <;>
      cases color <;>
      simp_all [IncidenceIsLocal,
        tripleSite, redElementSite, greenElementSite, blueElementSite,
        redClauseTerminal, greenClauseTerminal, blueClauseTerminal,
        sourceVariableSiteDrawing, variableSiteDrawing,
        variableSiteReference, variableSiteReferenceBase,
        variableSiteElementPosition, activeVariableSiteTriple,
        variableSiteTripleOfTyped, fixedRedVariableSiteElement,
        FixedRedConnector.reference,
        FixedRedConnectorTriple.references,
        assembledTypedReferenceTargetPosition,
        tripleReferences, fixedRedTripleReferences,
        fixedRedRedElement, fixedRedGreenElement, fixedRedBlueElement,
        firstCycleLinkSlot, secondCycleLinkSlot,
        assembledRedElementPosition,
        assembledGreenElementPosition,
        assembledBlueElementPosition,
        fixedRedInternalSitePosition,
        fixedRedInternalRedLocalElement,
        fixedRedInternalGreenLocalElement,
        fixedRedInternalBlueLocalElement,
        ThreeStrandRouting.periodTranslation,
        occurrenceVariableSiteSlot, Cell.add, Cell.scale]

/-- Every translated ordinary variable-site prefix is rectilinear. -/
theorem assembledOrdinaryPrefix_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.ordinary atom slot variant localTriple) location.2.2
          color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact typedVariableSiteRoute_orthogonal source atom location.1
      slot location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color segment segmentMember
  exact localOrthogonal.translate (routing.variableOrigin atom)

/-- Every translated fixed-red variable-site prefix is rectilinear. -/
theorem assembledFixedRedPrefix_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledFixedRedPrefix routing atom slot localTriple
        member color) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (typedVariableSiteRoute source atom location.1 slot location.2.1
          (.fixedRed atom slot localTriple) location.2.2 color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact typedVariableSiteRoute_orthogonal source atom location.1
      slot location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color segment segmentMember
  exact localOrthogonal.translate (routing.variableOrigin atom)

/-- Every translated clause-core route is rectilinear. -/
theorem assembledClauseRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledClauseRoute routing clauseIndex set color) := by
  have localOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (orientedIncidenceLocalRoute
          source (.clause clauseIndex set) color) := by
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments _).mpr
    intro segment segmentMember
    exact orientedIncidenceLocalRoute_orthogonal source
      (.clause clauseIndex set) color segment segmentMember
  exact localOrthogonal.translate (routing.clauseOrigin clauseIndex)

/-- If an ordinary incidence is the routed connector incidence, its
translated finite prefix ends exactly at the corresponding certified
corridor port. -/
theorem assembledOrdinaryPrefix_getLast_routed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor)
    (routed :
      Triple.ordinary atom slot variant localTriple =
        routedOccurrenceTriple source atom slot color) :
    let location :=
      ordinaryTriple_location source atom slot variant localTriple member
    let entry : ActiveOccurrenceEntry source :=
      ⟨(atom, slot),
        (mem_occurrenceEntries_iff source atom slot).mpr
          ⟨location.1, location.2.1⟩⟩
    (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color).getLast? =
      some (Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color
  simp only [assembledOrdinaryPrefix,
    PeriodicOrthocrossing.translatePolyline, List.getLast?_map,
    endpoints.2, Option.map_some]
  congr 2
  simp only [routedVariablePortPosition,
    routedActiveVariableSiteTriple]
  congr 2
  apply Subtype.ext
  exact congrArg variableSiteTripleOfTyped routed

/-- The analogous fixed-red routed prefix ends at its certified RGB
corridor port. -/
theorem assembledFixedRedPrefix_getLast_routed
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor)
    (routed :
      Triple.fixedRed atom slot localTriple =
        routedOccurrenceTriple source atom slot color) :
    let location :=
      fixedRedTriple_location source atom slot localTriple member
    let entry : ActiveOccurrenceEntry source :=
      ⟨(atom, slot),
        (mem_occurrenceEntries_iff source atom slot).mpr
          ⟨location.1, location.2.1⟩⟩
    (assembledFixedRedPrefix routing atom slot localTriple
        member color).getLast? =
      some (Cell.add (routing.variableOrigin atom)
        (routedVariablePortPosition source entry color)) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color
  simp only [assembledFixedRedPrefix,
    PeriodicOrthocrossing.translatePolyline, List.getLast?_map,
    endpoints.2, Option.map_some]
  congr 2
  simp only [routedVariablePortPosition,
    routedActiveVariableSiteTriple]
  congr 2
  apply Subtype.ext
  exact congrArg variableSiteTripleOfTyped routed

/-- A local ordinary prefix ends at its typed zero-offset element target. -/
theorem assembledOrdinaryPrefix_getLast_local
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor)
    (localIncidence :
      IncidenceIsLocal source color
        (.ordinary atom slot variant localTriple)) :
    (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color).getLast? =
      some (assembledTypedReferenceTargetPosition routing
        (.ordinary atom slot variant localTriple) color) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color
  have targetEq :=
    activeOrdinaryReference_position_local routing atom location.1
      slot location.2.1 variant localTriple location.2.2 color
      localIncidence
  have translated :=
    congrArg (Option.map (Cell.add (routing.variableOrigin atom)))
      endpoints.2
  simpa [assembledOrdinaryPrefix,
    PeriodicOrthocrossing.translatePolyline] using
      translated.trans (congrArg some targetEq)

/-- A local fixed-red prefix ends at its typed zero-offset element target. -/
theorem assembledFixedRedPrefix_getLast_local
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor)
    (localIncidence :
      IncidenceIsLocal source color
        (.fixedRed atom slot localTriple)) :
    (assembledFixedRedPrefix routing atom slot localTriple
        member color).getLast? =
      some (assembledTypedReferenceTargetPosition routing
        (.fixedRed atom slot localTriple) color) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have endpoints :=
    typedVariableSiteRoute_endpoints source atom location.1 slot
      location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color
  have targetEq :=
    activeFixedRedReference_position_local routing atom location.1
      slot location.2.1 localTriple location.2.2 color localIncidence
  have translated :=
    congrArg (Option.map (Cell.add (routing.variableOrigin atom)))
      endpoints.2
  simpa [assembledFixedRedPrefix,
    PeriodicOrthocrossing.translatePolyline] using
      translated.trans (congrArg some targetEq)

/-- Complete route of one active typed incidence. -/
def assembledTypedIncidenceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) : List Cell :=
  match tripleEq : triple.1 with
  | .ordinary atom slot variant localTriple =>
      let member :
          Triple.ordinary atom slot variant localTriple ∈
            triples source :=
        tripleEq ▸ triple.2
      let prefixRoute :=
        assembledOrdinaryPrefix routing atom slot variant localTriple
          member color
      if _routed :
          Triple.ordinary atom slot variant localTriple =
            routedOccurrenceTriple source atom slot color then
        let location :=
          ordinaryTriple_location source atom slot variant localTriple
            member
        let entry : ActiveOccurrenceEntry source :=
          ⟨(atom, slot),
            (mem_occurrenceEntries_iff source atom slot).mpr
              ⟨location.1, location.2.1⟩⟩
        joinAtEndpoint prefixRoute (routing.route entry color)
      else
        prefixRoute
  | .fixedRed atom slot localTriple =>
      let member :
          Triple.fixedRed atom slot localTriple ∈ triples source :=
        tripleEq ▸ triple.2
      let prefixRoute :=
        assembledFixedRedPrefix routing atom slot localTriple
          member color
      if _routed :
          Triple.fixedRed atom slot localTriple =
            routedOccurrenceTriple source atom slot color then
        let location :=
          fixedRedTriple_location source atom slot localTriple member
        let entry : ActiveOccurrenceEntry source :=
          ⟨(atom, slot),
            (mem_occurrenceEntries_iff source atom slot).mpr
              ⟨location.1, location.2.1⟩⟩
        joinAtEndpoint prefixRoute (routing.route entry color)
      else
        prefixRoute
  | .clause clauseIndex set =>
      assembledClauseRoute routing clauseIndex set color

/-- Every complete typed incidence route has the exact typed endpoints,
including the physical translation represented by its periodic reference. -/
theorem assembledTypedIncidenceRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) :
    (assembledTypedIncidenceRoute routing triple color).head? =
        some (assembledTriplePosition routing triple.1) ∧
      (assembledTypedIncidenceRoute routing triple color).getLast? =
        some (assembledTypedReferenceTargetPosition
          routing triple.1 color) := by
  unfold assembledTypedIncidenceRoute
  split
  next atom slot variant localTriple tripleEq =>
    have triplePositionEq :=
      congrArg (assembledTriplePosition routing) tripleEq
    have referenceTargetEq :=
      congrArg
        (fun typed =>
          assembledTypedReferenceTargetPosition routing typed color)
        tripleEq
    let member :
        Triple.ordinary atom slot variant localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    let location :=
      ordinaryTriple_location source atom slot variant localTriple member
    split
    next routed =>
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      constructor
      · exact (joinAtEndpoint_head?
          (assembledOrdinaryPrefix_head routing atom slot variant
            localTriple member color)).trans
              (congrArg some triplePositionEq.symm)
      · have joined :=
          joinAtEndpoint_getLast?
            (assembledOrdinaryPrefix_getLast_routed routing atom slot
              variant localTriple member color routed)
            (routing.routeEndpoints entry color).1
            (routing.routeEndpoints entry color).2
        have targetEq :
            routedClauseTargetPosition source routing.period
                routing.clauseOrigin entry color =
              assembledTypedReferenceTargetPosition routing
                (.ordinary atom slot variant localTriple) color :=
          (routedClauseTargetPosition_eq_typedReference
            routing entry color).trans
              (congrArg
                (fun typed =>
                  assembledTypedReferenceTargetPosition
                    routing typed color) routed).symm
        exact (joined.trans (congrArg some targetEq)).trans
          (congrArg some referenceTargetEq.symm)
    next notRouted =>
      constructor
      · exact (assembledOrdinaryPrefix_head routing atom slot variant
          localTriple member color).trans
            (congrArg some triplePositionEq.symm)
      · rcases occurrenceTriple_incidence_local_or_routed source atom
          slot (.ordinary atom slot variant localTriple)
          location.2.2 color with localIncidence | routed
        · exact (assembledOrdinaryPrefix_getLast_local routing atom slot
            variant localTriple member color localIncidence).trans
              (congrArg some referenceTargetEq.symm)
        · exact False.elim (notRouted routed)
  next atom slot localTriple tripleEq =>
    have triplePositionEq :=
      congrArg (assembledTriplePosition routing) tripleEq
    have referenceTargetEq :=
      congrArg
        (fun typed =>
          assembledTypedReferenceTargetPosition routing typed color)
        tripleEq
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    let location :=
      fixedRedTriple_location source atom slot localTriple member
    split
    next routed =>
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      constructor
      · exact (joinAtEndpoint_head?
          (assembledFixedRedPrefix_head routing atom slot localTriple
            member color)).trans
              (congrArg some triplePositionEq.symm)
      · have joined :=
          joinAtEndpoint_getLast?
            (assembledFixedRedPrefix_getLast_routed routing atom slot
              localTriple member color routed)
            (routing.routeEndpoints entry color).1
            (routing.routeEndpoints entry color).2
        have targetEq :
            routedClauseTargetPosition source routing.period
                routing.clauseOrigin entry color =
              assembledTypedReferenceTargetPosition routing
                (.fixedRed atom slot localTriple) color :=
          (routedClauseTargetPosition_eq_typedReference
            routing entry color).trans
              (congrArg
                (fun typed =>
                  assembledTypedReferenceTargetPosition
                    routing typed color) routed).symm
        exact (joined.trans (congrArg some targetEq)).trans
          (congrArg some referenceTargetEq.symm)
    next notRouted =>
      constructor
      · exact (assembledFixedRedPrefix_head routing atom slot localTriple
          member color).trans
            (congrArg some triplePositionEq.symm)
      · rcases occurrenceTriple_incidence_local_or_routed source atom
          slot (.fixedRed atom slot localTriple)
          location.2.2 color with localIncidence | routed
        · exact (assembledFixedRedPrefix_getLast_local routing atom slot
            localTriple member color localIncidence).trans
              (congrArg some referenceTargetEq.symm)
        · exact False.elim (notRouted routed)
  next clauseIndex set tripleEq =>
    have endpoints :=
      assembledClauseRoute_endpoints routing clauseIndex set color
    have triplePositionEq :=
      congrArg (assembledTriplePosition routing) tripleEq
    have referenceTargetEq :=
      congrArg
        (fun typed =>
          assembledTypedReferenceTargetPosition routing typed color)
        tripleEq
    exact
      ⟨endpoints.1.trans (congrArg some triplePositionEq.symm),
        endpoints.2.trans (congrArg some referenceTargetEq.symm)⟩

/-- Every complete typed incidence route is rectilinear. -/
theorem assembledTypedIncidenceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (triple : {triple : Triple Variable // triple ∈ triples source})
    (color : WireColor) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledTypedIncidenceRoute routing triple color) := by
  unfold assembledTypedIncidenceRoute
  split
  next atom slot variant localTriple tripleEq =>
    let member :
        Triple.ordinary atom slot variant localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        ordinaryTriple_location source atom slot variant localTriple
          member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      apply
        (assembledOrdinaryPrefix_orthogonal routing atom slot variant
          localTriple member color).joinAtEndpoint
          (routing.route_orthogonal entry color)
      · exact assembledOrdinaryPrefix_getLast_routed routing atom slot
          variant localTriple member color routed
      · exact (routing.route_endpoints entry color).1
    next notRouted =>
      exact assembledOrdinaryPrefix_orthogonal routing atom slot variant
        localTriple member color
  next atom slot localTriple tripleEq =>
    let member :
        Triple.fixedRed atom slot localTriple ∈ triples source :=
      tripleEq ▸ triple.2
    split
    next routed =>
      let location :=
        fixedRedTriple_location source atom slot localTriple member
      let entry : ActiveOccurrenceEntry source :=
        ⟨(atom, slot),
          (mem_occurrenceEntries_iff source atom slot).mpr
            ⟨location.1, location.2.1⟩⟩
      apply
        (assembledFixedRedPrefix_orthogonal routing atom slot localTriple
          member color).joinAtEndpoint
          (routing.route_orthogonal entry color)
      · exact assembledFixedRedPrefix_getLast_routed routing atom slot
          localTriple member color routed
      · exact (routing.route_endpoints entry color).1
    next notRouted =>
      exact assembledFixedRedPrefix_orthogonal routing atom slot
        localTriple member color
  next clauseIndex set tripleEq =>
    exact assembledClauseRoute_orthogonal
      routing clauseIndex set color

/-- Route selected by one encoded incidence tag.  Genuine tags always take
the in-range branch; the fallback makes the function total. -/
def assembledRouteAtTag
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag) : List Cell :=
  if indexLt : tag.tripleIndex < (triples source).length then
    assembledTypedIncidenceRoute routing
      ⟨(triples source)[tag.tripleIndex]'indexLt,
        List.getElem_mem indexLt⟩
      tag.color
  else
    []

/-- Edge-route list in the encoded incidence-tag order. -/
def assembledEdgeRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) : List (List Cell) :=
  (encodedProblem source).incidenceTags.map
    (assembledRouteAtTag routing)

/-- The assembled route list has exactly one entry per encoded incidence
graph edge. -/
theorem assembledEdgeRoutes_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source) :
    (assembledEdgeRoutes routing).length =
      (encodedProblem source).incidenceGraph.edges.length := by
  simp [assembledEdgeRoutes]

/-- Every tag-selected route is rectilinear, including the empty fallback
for an out-of-range tag. -/
theorem assembledRouteAtTag_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (assembledRouteAtTag routing tag) := by
  unfold assembledRouteAtTag
  split
  · exact assembledTypedIncidenceRoute_orthogonal routing _ tag.color
  · simp [PeriodicOrthocrossing.OrthogonalPolyline]

/-- A genuine encoded tag retrieves the active typed triple at the same
index and therefore inherits its exact typed endpoints. -/
theorem assembledRouteAtTag_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember : tag ∈ (encodedProblem source).incidenceTags) :
    let indexLt : tag.tripleIndex < (triples source).length := by
      simpa [encodedProblem, TypedProblem.encode, problem] using
        PeriodicThreeDM.incidenceTag_tripleIndex_lt
          (encodedProblem source) tagMember
    let active :
        {triple : Triple Variable // triple ∈ triples source} :=
      ⟨(triples source)[tag.tripleIndex]'indexLt,
        List.getElem_mem indexLt⟩
    (assembledRouteAtTag routing tag).head? =
        some (assembledTriplePosition routing active.1) ∧
      (assembledRouteAtTag routing tag).getLast? =
        some (assembledTypedReferenceTargetPosition
          routing active.1 tag.color) := by
  have indexLt : tag.tripleIndex < (triples source).length := by
    simpa [encodedProblem, TypedProblem.encode, problem] using
      PeriodicThreeDM.incidenceTag_tripleIndex_lt
        (encodedProblem source) tagMember
  simp only [assembledRouteAtTag, dif_pos indexLt]
  exact assembledTypedIncidenceRoute_endpoints routing
    ⟨(triples source)[tag.tripleIndex]'indexLt,
      List.getElem_mem indexLt⟩ tag.color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
