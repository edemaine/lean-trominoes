/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonFanClockwiseOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans

/-!
# Clockwise order of source variable ribbon fans

Continuous source planarity already makes the outgoing directions at one
variable genuine and pairwise distinct.  This file transfers those facts
from the occurrence-family API to the finite coordinated-fan record.
Consequently the variable side of the fan-table obligation reduces exactly
to the cyclic order of the three source occurrences; variables of degree one
or two require no additional premise.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM PeriodicOrthocrossing

namespace VariableRibbonFanData

/-- The active prefix of the finite fan is exactly the source variable's
used occurrence-slot prefix. -/
theorem sourceVariableRibbonFanData_outerData_slotActive_iff
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (slot : VariableSiteSlot) :
    VariableOuterFanData.SlotActive
        (sourceVariableRibbonFanData
          presentation.toPlanarIncidencePresentation entry).outerData
        slot ↔
      variableSiteOccurrenceSlot slot ∈
        usedSlots source.erase entry.1.1 := by
  rcases usedSlots_cases_of_atom_mem
      source.erase entry.1.1 entry.atom_mem with
    one | twoOrThree
  · cases slot <;>
      simp [VariableOuterFanData.SlotActive, outerData,
        VariableOuterFanData.ofVariableRibbonFanData,
        sourceVariableRibbonFanData, sourceVariableRibbonCountPred,
        VariableOuterFanData.count, VariableSiteSlot.index,
        variableSiteOccurrenceSlot, one]
  · rcases twoOrThree with two | three
    · cases slot <;>
        simp [VariableOuterFanData.SlotActive, outerData,
          VariableOuterFanData.ofVariableRibbonFanData,
          sourceVariableRibbonFanData, sourceVariableRibbonCountPred,
          VariableOuterFanData.count, VariableSiteSlot.index,
          variableSiteOccurrenceSlot, two]
    · cases slot <;>
        simp [VariableOuterFanData.SlotActive, outerData,
          VariableOuterFanData.ofVariableRibbonFanData,
          sourceVariableRibbonFanData, sourceVariableRibbonCountPred,
          VariableOuterFanData.count, VariableSiteSlot.index,
          variableSiteOccurrenceSlot, three]

/-- The actual source occurrence represented by one active finite fan
slot. -/
def sourceVariableRibbonFanEntryAtActiveSlot
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (slot : VariableSiteSlot)
    (active :
      (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry)
        |>.outerData.SlotActive slot) :
    ActiveOccurrenceEntry source.erase :=
  ⟨(entry.1.1, variableSiteOccurrenceSlot slot),
    (mem_occurrenceEntries_iff source.erase
      entry.1.1 (variableSiteOccurrenceSlot slot)).mpr
        ⟨entry.atom_mem,
          (sourceVariableRibbonFanData_outerData_slotActive_iff
            presentation entry slot).mp active⟩⟩

@[simp]
theorem sourceVariableRibbonFanEntryAtActiveSlot_atom
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (slot : VariableSiteSlot)
    (active :
      (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry)
        |>.outerData.SlotActive slot) :
    (sourceVariableRibbonFanEntryAtActiveSlot
      presentation entry slot active).1.1 = entry.1.1 :=
  rfl

@[simp]
theorem sourceVariableRibbonFanEntryAtActiveSlot_slot
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (slot : VariableSiteSlot)
    (active :
      (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry)
        |>.outerData.SlotActive slot) :
    (sourceVariableRibbonFanEntryAtActiveSlot
      presentation entry slot active).1.2 =
        variableSiteOccurrenceSlot slot :=
  rfl

/-- Source planarity discharges the genuine-and-distinct portion of every
finite source variable fan. -/
theorem sourceVariableRibbonFanData_outerData_isValid
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry).outerData.IsValid := by
  let planar := presentation.toPlanarIncidencePresentation
  let data := sourceVariableRibbonFanData planar entry
  constructor
  · intro slot active
    let candidate :=
      sourceVariableRibbonFanEntryAtActiveSlot
        presentation entry slot active
    have directionEq :=
      sourceVariableRibbonFanData_direction_of_same_atom
        planar entry candidate (by simp [candidate])
    have directionAtSlot :
        data.direction slot =
          occurrenceSourceVariableDirection planar candidate := by
      simpa [data, candidate] using directionEq
    have genuine :=
      occurrenceSourceVariableDirection_isGenuine
        planar candidate
    change (data.direction slot).IsGenuine
    rw [directionAtSlot]
    exact genuine
  · intro firstSlot secondSlot firstActive secondActive slotsDifferent
    let first :=
      sourceVariableRibbonFanEntryAtActiveSlot
        presentation entry firstSlot firstActive
    let second :=
      sourceVariableRibbonFanEntryAtActiveSlot
        presentation entry secondSlot secondActive
    have firstAtom : first.1.1 = entry.1.1 := by
      simp [first]
    have secondAtom : second.1.1 = entry.1.1 := by
      simp [second]
    have entriesDifferent : first ≠ second := by
      intro entriesEqual
      apply slotsDifferent
      have occurrenceSlotEqual :
          first.1.2 = second.1.2 :=
        congrArg
          (fun candidate : ActiveOccurrenceEntry source.erase =>
            candidate.1.2)
          entriesEqual
      calc
        firstSlot =
            occurrenceVariableSiteSlot
              (variableSiteOccurrenceSlot firstSlot) := by
          simp
        _ = occurrenceVariableSiteSlot
              (variableSiteOccurrenceSlot secondSlot) := by
          apply congrArg occurrenceVariableSiteSlot
          simpa [first, second] using occurrenceSlotEqual
        _ = secondSlot := by
          simp
    have directionsDifferent :=
      occurrenceSourceVariableDirections_ne_of_same_variable
        presentation entriesDifferent
          (firstAtom.trans secondAtom.symm)
    have firstDirection :=
      sourceVariableRibbonFanData_direction_of_same_atom
        planar entry first firstAtom
    have secondDirection :=
      sourceVariableRibbonFanData_direction_of_same_atom
        planar entry second secondAtom
    have firstDirectionAtSlot :
        data.direction firstSlot =
          occurrenceSourceVariableDirection planar first := by
      simpa [data, first] using firstDirection
    have secondDirectionAtSlot :
        data.direction secondSlot =
          occurrenceSourceVariableDirection planar second := by
      simpa [data, second] using secondDirection
    change data.direction firstSlot ≠ data.direction secondSlot
    rw [firstDirectionAtSlot, secondDirectionAtSlot]
    exact directionsDifferent

/-- A source variable fan is table-compatible exactly when its degree-three
case occurs in clockwise cyclic order. -/
theorem sourceVariableRibbonFanData_isClockwiseCompatible_iff
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry).IsClockwiseCompatible ↔
      ((sourceVariableRibbonFanData
          presentation.toPlanarIncidencePresentation entry).count = 3 →
        AxisDirection.InClockwiseOrder
          ((sourceVariableRibbonFanData
              presentation.toPlanarIncidencePresentation entry).direction
            .first)
          ((sourceVariableRibbonFanData
              presentation.toPlanarIncidencePresentation entry).direction
            .second)
          ((sourceVariableRibbonFanData
              presentation.toPlanarIncidencePresentation entry).direction
            .third)) := by
  unfold IsClockwiseCompatible
  rw [VariableOuterFanData.isClockwiseCompatible_iff]
  simp only [
    sourceVariableRibbonFanData_outerData_isValid presentation entry,
    true_and]
  rfl

/-- Degree-one and degree-two source variables need no cyclic-order
assumption. -/
theorem sourceVariableRibbonFanData_isClockwiseCompatible_of_count_ne_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (count :
      (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry).count ≠ 3) :
    (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry).IsClockwiseCompatible :=
  (sourceVariableRibbonFanData_isClockwiseCompatible_iff
    presentation entry).2 fun countThree =>
      (count countThree).elim

end VariableRibbonFanData

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
