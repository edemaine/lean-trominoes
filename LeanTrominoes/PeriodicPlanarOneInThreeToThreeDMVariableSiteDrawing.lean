/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMLocalDrawings
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSoundness
import LeanTrominoes.PlanarThreeDMVariableSiteDrawing

/-!
# Instantiating the finite variable-site drawings

The planar 3DM reduction has two descriptions of the same occurrence
positions.  The periodic assembly uses `OccurrenceSlot`, while the finite
geometric checker uses `VariableSiteSlot`.  This file identifies those
enumerations and instantiates the checked one-, two-, or three-occurrence
drawing at every occurring source variable.

Only relative coordinates are chosen here.  A later global assembly
translates the resulting finite drawing into a reserved neighborhood of the
source variable vertex.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- The occurrence-slot enumeration used by the periodic assembly, viewed
as a slot of the finite variable-site drawing. -/
def occurrenceVariableSiteSlot : OccurrenceSlot → VariableSiteSlot
  | .first => .first
  | .second => .second
  | .third => .third

/-- The inverse identification of the two three-slot enumerations. -/
def variableSiteOccurrenceSlot : VariableSiteSlot → OccurrenceSlot
  | .first => .first
  | .second => .second
  | .third => .third

@[simp]
theorem variableSiteOccurrenceSlot_occurrenceVariableSiteSlot
    (slot : OccurrenceSlot) :
    variableSiteOccurrenceSlot (occurrenceVariableSiteSlot slot) = slot := by
  cases slot <;> rfl

@[simp]
theorem occurrenceVariableSiteSlot_variableSiteOccurrenceSlot
    (slot : VariableSiteSlot) :
    occurrenceVariableSiteSlot (variableSiteOccurrenceSlot slot) = slot := by
  cases slot <;> rfl

@[simp]
theorem occurrenceVariableSiteSlot_index (slot : OccurrenceSlot) :
    (occurrenceVariableSiteSlot slot).index = slot.index := by
  cases slot <;> rfl

/-- Number of active occurrence modules at one source variable. -/
def sourceVariableSiteCount
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) : Nat :=
  (usedSlots source atom).length

/-- Connector-kind pattern supplied to the finite drawing.  Inactive slots
are deliberately filled in the same way as the checked one- and two-site
specializations, so their validity theorems apply definitionally. -/
def sourceVariableSiteKind
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    VariableSiteSlot → VariableConnectorKind :=
  match usedSlots source atom with
  | [.first] =>
      fun _ => occurrenceConnectorKind source atom .first
  | [.first, .second] =>
      fun slot =>
        if slot = .first then
          occurrenceConnectorKind source atom .first
        else
          occurrenceConnectorKind source atom .second
  | _ =>
      fun slot =>
        if slot = .first then
          occurrenceConnectorKind source atom .first
        else if slot = .second then
          occurrenceConnectorKind source atom .second
        else
          occurrenceConnectorKind source atom .third

/-- Literal-polarity pattern supplied to the finite drawing. -/
def sourceVariableSitePolarity
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :
    VariableSiteSlot → Bool :=
  match usedSlots source atom with
  | [.first] =>
      fun _ => occurrencePolarity source atom .first
  | [.first, .second] =>
      fun slot =>
        if slot = .first then
          occurrencePolarity source atom .first
        else
          occurrencePolarity source atom .second
  | _ =>
      fun slot =>
        if slot = .first then
          occurrencePolarity source atom .first
        else if slot = .second then
          occurrencePolarity source atom .second
        else
          occurrencePolarity source atom .third

/-- An active source slot has the connector kind advertised to the finite
site drawing. -/
theorem sourceVariableSiteKind_active
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    sourceVariableSiteKind source atom
        (occurrenceVariableSiteSlot slot) =
      occurrenceConnectorKind source atom slot := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · cases slot <;>
      simp_all [sourceVariableSiteKind]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp_all [sourceVariableSiteKind, occurrenceVariableSiteSlot]
    · cases slot <;>
        simp_all [sourceVariableSiteKind, occurrenceVariableSiteSlot]

/-- An active source slot has the polarity advertised to the finite site
drawing. -/
theorem sourceVariableSitePolarity_active
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    sourceVariableSitePolarity source atom
        (occurrenceVariableSiteSlot slot) =
      occurrencePolarity source atom slot := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · cases slot <;>
      simp_all [sourceVariableSitePolarity]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp_all [sourceVariableSitePolarity, occurrenceVariableSiteSlot]
    · cases slot <;>
        simp_all [sourceVariableSitePolarity, occurrenceVariableSiteSlot]

/-- An active periodic occurrence slot lies in the active prefix of the
finite drawing. -/
theorem occurrenceVariableSiteSlot_index_lt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    (occurrenceVariableSiteSlot slot).index <
      sourceVariableSiteCount source atom := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · cases slot <;>
      simp_all [sourceVariableSiteCount, occurrenceVariableSiteSlot,
        VariableSiteSlot.index]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp_all [sourceVariableSiteCount, occurrenceVariableSiteSlot,
          VariableSiteSlot.index]
    · cases slot <;>
        simp_all [sourceVariableSiteCount, occurrenceVariableSiteSlot,
          VariableSiteSlot.index]

/-- The cyclic successor used by the periodic assembly agrees with the
finite variable-site successor on every active slot. -/
theorem occurrenceVariableSiteSlot_nextUsedSlot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom) :
    occurrenceVariableSiteSlot (nextUsedSlot source atom slot) =
      nextVariableSiteSlot (sourceVariableSiteCount source atom)
        (occurrenceVariableSiteSlot slot) := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · cases slot <;>
      simp_all [nextUsedSlot, sourceVariableSiteCount,
        occurrenceVariableSiteSlot, nextVariableSiteSlot]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp_all [nextUsedSlot, sourceVariableSiteCount,
          occurrenceVariableSiteSlot, nextVariableSiteSlot]
    · cases slot <;>
        simp_all [nextUsedSlot, sourceVariableSiteCount,
          occurrenceVariableSiteSlot, nextVariableSiteSlot]

/-- Forget the periodic names on a variable-module triple while retaining
its finite site slot and local template name.  The clause fallback is never
used by the variable-site interface. -/
def variableSiteTripleOfTyped
    {Variable : Type*} : Triple Variable → VariableSiteTriple
  | .ordinary _ slot variant triple =>
      .ordinary (occurrenceVariableSiteSlot slot) variant triple
  | .fixedRed _ slot triple =>
      .fixedRed (occurrenceVariableSiteSlot slot) triple
  | .clause _ _ =>
      .ordinary .first .fixedGreen .first

/-- Every triple in an active occurrence block satisfies the finite
drawing's active-triple predicate. -/
theorem variableSiteTripleOfTyped_matches
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot) :
    (variableSiteTripleOfTyped triple).MatchesKind
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) := by
  have active :=
    occurrenceVariableSiteSlot_index_lt
      source atom atomMember slot slotMember
  have active' :
      slot.index < sourceVariableSiteCount source atom := by
    simpa using active
  have kindAt :=
    sourceVariableSiteKind_active
      source atom atomMember slot slotMember
  cases kindEq : occurrenceConnectorKind source atom slot <;>
    simp [occurrenceTriples, kindEq, allOrdinaryTriples,
      allFixedRedTriples] at tripleMember
  · rcases tripleMember with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [variableSiteTripleOfTyped,
        VariableSiteTriple.MatchesKind, active', kindAt, kindEq]
  · rcases tripleMember with (rfl | rfl | rfl) <;>
      simp [variableSiteTripleOfTyped,
        VariableSiteTriple.MatchesKind, active', kindAt, kindEq]
  · rcases tripleMember with (rfl | rfl | rfl) <;>
      simp [variableSiteTripleOfTyped,
        VariableSiteTriple.MatchesKind, active', kindAt, kindEq]

/-- The active finite triple corresponding to one listed periodic
variable-module triple. -/
def activeVariableSiteTriple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot) :
    ActiveVariableSiteTriple
      (sourceVariableSiteCount source atom)
      (sourceVariableSiteKind source atom) :=
  ⟨variableSiteTripleOfTyped triple,
    variableSiteTripleOfTyped_matches source atom atomMember slot
      slotMember triple tripleMember⟩

/-- The finite drawing instantiated at one source variable. -/
def sourceVariableSiteDrawing
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (atom : Variable) :=
  variableSiteDrawing
    (sourceVariableSiteCount source atom)
    (sourceVariableSiteKind source atom)
    (sourceVariableSitePolarity source atom)

/-- Every occurring source variable instantiates one of the exhaustively
checked one-, two-, or three-module drawings. -/
theorem sourceVariableSiteDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source) :
    (sourceVariableSiteDrawing source atom).IsValid := by
  rcases usedSlots_cases_of_atom_mem source atom atomMember with
    one | twoOrThree
  · unfold sourceVariableSiteDrawing sourceVariableSiteCount
      sourceVariableSiteKind sourceVariableSitePolarity
    rw [one]
    exact
      (all_oneVariableSiteDrawing_isValid
        (occurrenceConnectorKind source atom .first)
        (occurrencePolarity source atom .first))
  · rcases twoOrThree with two | three
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [two]
      exact
        (all_twoVariableSiteDrawing_isValid
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second))
    · unfold sourceVariableSiteDrawing sourceVariableSiteCount
        sourceVariableSiteKind sourceVariableSitePolarity
      rw [three]
      exact
        (all_threeVariableSiteDrawing_isValid
          (occurrenceConnectorKind source atom .first)
          (occurrenceConnectorKind source atom .second)
          (occurrenceConnectorKind source atom .third)
          (occurrencePolarity source atom .first)
          (occurrencePolarity source atom .second)
          (occurrencePolarity source atom .third))

/-- Relative route of one actual variable-module incidence in the complete
finite site drawing. -/
def typedVariableSiteRoute
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor) : List Cell :=
  (sourceVariableSiteDrawing source atom).route
    (activeVariableSiteTriple source atom atomMember slot slotMember
      triple tripleMember) color

/-- The instantiated route starts at the corresponding finite triple
position and ends at its assembled finite element position. -/
theorem typedVariableSiteRoute_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor) :
    let active :=
      activeVariableSiteTriple source atom atomMember slot slotMember
        triple tripleMember
    (typedVariableSiteRoute source atom atomMember slot slotMember
        triple tripleMember color).head? =
        some ((sourceVariableSiteDrawing source atom).triplePosition
          active) ∧
      (typedVariableSiteRoute source atom atomMember slot slotMember
        triple tripleMember color).getLast? =
        some ((sourceVariableSiteDrawing source atom).elementPosition
          ((sourceVariableSiteDrawing source atom).reference
            active color)) := by
  exact (sourceVariableSiteDrawing_isValid
    source atom atomMember).1
      (activeVariableSiteTriple source atom atomMember slot slotMember
        triple tripleMember, color)

/-- Every segment of an instantiated variable-site route is axis-aligned. -/
theorem typedVariableSiteRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor)
    (segment : GridSegment)
    (segmentMember :
      segment ∈ gridPolylineSegments
        (typedVariableSiteRoute source atom atomMember slot slotMember
          triple tripleMember color)) :
    segment.IsAxisAligned := by
  exact (sourceVariableSiteDrawing_isValid
    source atom atomMember).2.1
      (activeVariableSiteTriple source atom atomMember slot slotMember
        triple tripleMember, color) segment segmentMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
