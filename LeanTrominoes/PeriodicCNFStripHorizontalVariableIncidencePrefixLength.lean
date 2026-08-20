/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalVariableIncidenceLocalRouteSemanticBridge

/-! # Nondegeneracy of horizontal variable-incidence prefixes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A list whose displayed endpoints differ contains at least one edge. -/
private theorem length_ge_two_of_head_getLast_ne
    {α : Type*} {items : List α} {first last : α}
    (headEq : items.head? = some first)
    (lastEq : items.getLast? = some last)
    (different : first ≠ last) :
    2 ≤ items.length := by
  cases items with
  | nil => simp at headEq
  | cons item rest =>
      cases rest with
      | nil =>
          simp at headEq lastEq
          exact (different (headEq.symm.trans lastEq)).elim
      | cons next rest => simp

/-- Every incidence route in a certified finite variable-site drawing has
at least one edge. -/
theorem typedVariableSiteRoute_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor) :
    2 ≤ (typedVariableSiteRoute source atom atomMember slot slotMember
      triple tripleMember color).length := by
  let drawing := sourceVariableSiteDrawing source atom
  let active := activeVariableSiteTriple source atom atomMember slot
    slotMember triple tripleMember
  have valid := sourceVariableSiteDrawing_isValid source atom atomMember
  have endpoints := typedVariableSiteRoute_endpoints source atom atomMember
    slot slotMember triple tripleMember color
  have distinct := valid.2.2.2.2.2
  exact length_ge_two_of_head_getLast_ne endpoints.1 endpoints.2
    (distinct.2.2 active (drawing.reference active color))

/-- The executable local route attached to an active occurrence has at
least one edge. -/
theorem horizontalVariableIncidenceLocalRouteComputed_length_ge_two
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (tripleMember : triple ∈ occurrenceTriples
      (horizontalSemanticNormalizedRibbonSource source).erase
      entry.1.1 entry.1.2)
    (color : WireColor) :
    2 ≤ (horizontalVariableIncidenceLocalRouteComputed
      (((source, entry.1.1), triple), color)).length := by
  rw [horizontalVariableIncidenceLocalRouteComputed_eq_semantic
    source entry triple tripleMember color]
  exact typedVariableSiteRoute_length_ge_two
    (horizontalSemanticNormalizedRibbonSource source).erase
    entry.1.1 entry.atom_mem entry.1.2 entry.slot_mem
    triple tripleMember color

/-- A translated ordinary variable-incidence prefix has at least one edge. -/
theorem horizontalOrdinaryVariableIncidencePrefixComputed_length_ge_two
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member : Triple.ordinary atom slot variant localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    2 ≤ (horizontalVariableIncidencePrefixComputed
      (((source, atom),
        Triple.ordinary atom slot variant localTriple), color)).length := by
  let location := ordinaryTriple_location
    (horizontalSemanticNormalizedRibbonSource source).erase
    atom slot variant localTriple member
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨location.1, location.2.1⟩⟩
  have localLength :=
    horizontalVariableIncidenceLocalRouteComputed_length_ge_two
      source entry (Triple.ordinary atom slot variant localTriple)
      location.2.2 color
  simpa only [horizontalVariableIncidencePrefixComputed,
    PeriodicOrthocrossing.translatePolyline, List.length_map,
    entry] using localLength

/-- A translated fixed-red variable-incidence prefix has at least one edge. -/
theorem horizontalFixedRedVariableIncidencePrefixComputed_length_ge_two
    (source : PeriodicCNF Nat)
    (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member : Triple.fixedRed atom slot localTriple ∈
      triples (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    2 ≤ (horizontalVariableIncidencePrefixComputed
      (((source, atom), Triple.fixedRed atom slot localTriple), color)).length := by
  let location := fixedRedTriple_location
    (horizontalSemanticNormalizedRibbonSource source).erase
    atom slot localTriple member
  let entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase :=
    ⟨(atom, slot),
      (mem_occurrenceEntries_iff
        (horizontalSemanticNormalizedRibbonSource source).erase
        atom slot).mpr ⟨location.1, location.2.1⟩⟩
  have localLength :=
    horizontalVariableIncidenceLocalRouteComputed_length_ge_two
      source entry (Triple.fixedRed atom slot localTriple)
      location.2.2 color
  simpa only [horizontalVariableIncidencePrefixComputed,
    PeriodicOrthocrossing.translatePolyline, List.length_map,
    entry] using localLength

end PeriodicCNFStripReduction
end LeanTrominoes
