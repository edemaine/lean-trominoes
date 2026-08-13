/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans

/-!
# Source variable data for coordinated ribbon fans

The finite variable-fan tables are indexed by an abstract
`VariableRibbonFanData`.  This file constructs that data from one actual
active occurrence of a positioned periodic exact-one source.

The active prefix, connector kinds, polarities, and endpoint directions are
all read from the source.  The construction is total by using the supplied
active occurrence as a fallback for inactive finite slots; every theorem
below concerns active slots, where the fallback is never observed.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Predecessor of the one-, two-, or three-slot source variable count. -/
def sourceVariableRibbonCountPred
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) : Fin 3 :=
  match usedSlots source atom with
  | [.first] => 0
  | [.first, .second] => 1
  | _ => 2

/-- Finite coordinated-fan data read from one actual source variable.

The result depends only on `entry.1.1`.  Active slots look up their genuine
source-route directions; inactive slots use the fixed north fallback and are
never inspected by a certified fan. -/
noncomputable def sourceVariableRibbonFanData
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    VariableRibbonFanData where
  countPred :=
    sourceVariableRibbonCountPred source.erase entry.1.1
  kind :=
    sourceVariableSiteKind source.erase entry.1.1
  polarity :=
    sourceVariableSitePolarity source.erase entry.1.1
  direction := fun slot =>
    let occurrenceSlot := variableSiteOccurrenceSlot slot
    if member :
        (entry.1.1, occurrenceSlot) ∈
          occurrenceEntries source.erase then
      occurrenceSourceVariableDirection presentation
        ⟨(entry.1.1, occurrenceSlot), member⟩
    else
      .north

namespace VariableRibbonFanData

/-- Occurrence-specific construction is only a convenient way to obtain
membership evidence: any two active occurrences of the same variable produce
literally the same finite fan data. -/
theorem sourceVariableRibbonFanData_eq_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (first second : ActiveOccurrenceEntry source.erase)
    (sameAtom : first.1.1 = second.1.1) :
    sourceVariableRibbonFanData presentation first =
      sourceVariableRibbonFanData presentation second := by
  unfold sourceVariableRibbonFanData
  cases first with
  | mk firstValue firstMember =>
      cases second with
      | mk secondValue secondMember =>
          cases firstValue with
          | mk firstAtom firstSlot =>
              cases secondValue with
              | mk secondAtom secondSlot =>
                  simp only at sameAtom
                  subst secondAtom
                  rfl

/-- The finite source data has exactly the source variable's active slot
count. -/
@[simp]
theorem sourceVariableRibbonFanData_count
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData presentation entry).count =
      sourceVariableSiteCount source.erase entry.1.1 := by
  rcases usedSlots_cases_of_atom_mem
      source.erase entry.1.1 entry.atom_mem with
    one | twoOrThree
  · simp [sourceVariableRibbonFanData,
      sourceVariableRibbonCountPred,
      sourceVariableSiteCount, one, count]
  · rcases twoOrThree with two | three
    · simp [sourceVariableRibbonFanData,
        sourceVariableRibbonCountPred,
        sourceVariableSiteCount, two, count]
    · simp [sourceVariableRibbonFanData,
        sourceVariableRibbonCountPred,
        sourceVariableSiteCount, three, count]

/-- Every actual source occurrence occupies an active slot of its finite fan
data. -/
theorem sourceVariableRibbonFanData_slotActive
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData presentation entry).SlotActive
      (occurrenceVariableSiteSlot entry.1.2) := by
  unfold SlotActive
  rw [sourceVariableRibbonFanData_count]
  exact occurrenceVariableSiteSlot_index_lt
    source.erase entry.1.1 entry.atom_mem
    entry.1.2 entry.slot_mem

/-- Every occurrence of the same source variable is active in a record
built from any one of its occurrences. -/
theorem sourceVariableRibbonFanData_slotActive_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1) :
    (sourceVariableRibbonFanData presentation base).SlotActive
      (occurrenceVariableSiteSlot candidate.1.2) := by
  unfold SlotActive
  rw [sourceVariableRibbonFanData_count]
  have active := occurrenceVariableSiteSlot_index_lt
    source.erase candidate.1.1 candidate.atom_mem
    candidate.1.2 candidate.slot_mem
  simpa [sameAtom] using active

/-- On an active source occurrence, the finite fan records the actual
connector kind. -/
@[simp]
theorem sourceVariableRibbonFanData_kind
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData presentation entry).kind
        (occurrenceVariableSiteSlot entry.1.2) =
      occurrenceConnectorKind
        source.erase entry.1.1 entry.1.2 := by
  exact sourceVariableSiteKind_active
    source.erase entry.1.1 entry.atom_mem
    entry.1.2 entry.slot_mem

/-- A record built from any occurrence agrees with every connector kind at
the same source variable. -/
theorem sourceVariableRibbonFanData_kind_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1) :
    (sourceVariableRibbonFanData presentation base).kind
        (occurrenceVariableSiteSlot candidate.1.2) =
      occurrenceConnectorKind
        source.erase candidate.1.1 candidate.1.2 := by
  have slotMember :
      candidate.1.2 ∈ usedSlots source.erase base.1.1 := by
    rw [← sameAtom]
    exact candidate.slot_mem
  simpa [sourceVariableRibbonFanData, sameAtom] using
    sourceVariableSiteKind_active
      source.erase base.1.1 base.atom_mem
      candidate.1.2 slotMember

/-- On an active source occurrence, the finite fan records the actual
literal polarity. -/
@[simp]
theorem sourceVariableRibbonFanData_polarity
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData presentation entry).polarity
        (occurrenceVariableSiteSlot entry.1.2) =
      occurrencePolarity source.erase entry.1.1 entry.1.2 := by
  exact sourceVariableSitePolarity_active
    source.erase entry.1.1 entry.atom_mem
    entry.1.2 entry.slot_mem

/-- A record built from any occurrence agrees with every literal polarity
at the same source variable. -/
theorem sourceVariableRibbonFanData_polarity_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1) :
    (sourceVariableRibbonFanData presentation base).polarity
        (occurrenceVariableSiteSlot candidate.1.2) =
      occurrencePolarity source.erase
        candidate.1.1 candidate.1.2 := by
  have slotMember :
      candidate.1.2 ∈ usedSlots source.erase base.1.1 := by
    rw [← sameAtom]
    exact candidate.slot_mem
  simpa [sourceVariableRibbonFanData, sameAtom] using
    sourceVariableSitePolarity_active
      source.erase base.1.1 base.atom_mem
      candidate.1.2 slotMember

/-- On an active source occurrence, the finite fan records its genuine
outgoing route direction. -/
@[simp]
theorem sourceVariableRibbonFanData_direction
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData presentation entry).direction
        (occurrenceVariableSiteSlot entry.1.2) =
      occurrenceSourceVariableDirection presentation entry := by
  simp [sourceVariableRibbonFanData, entry.2]

/-- A record built from any occurrence of a variable records the direction
of every other active occurrence of that same variable. -/
theorem sourceVariableRibbonFanData_direction_of_same_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (base candidate : ActiveOccurrenceEntry source.erase)
    (sameAtom : candidate.1.1 = base.1.1) :
    (sourceVariableRibbonFanData presentation base).direction
        (occurrenceVariableSiteSlot candidate.1.2) =
      occurrenceSourceVariableDirection presentation candidate := by
  have member :
      (base.1.1, candidate.1.2) ∈ occurrenceEntries source.erase := by
    rw [← sameAtom]
    exact candidate.2
  simp only [sourceVariableRibbonFanData,
    variableSiteOccurrenceSlot_occurrenceVariableSiteSlot]
  rw [dif_pos member]
  congr 1
  apply Subtype.ext
  exact Prod.ext sameAtom.symm rfl

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
