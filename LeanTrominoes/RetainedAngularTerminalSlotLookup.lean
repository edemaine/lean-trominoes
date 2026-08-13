/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanAnnulusRefinedRoutes

/-!
# Looking up retained occurrences in the eight fan slots

The coordinated router is indexed by a bounded `Fin 8` slot, while source
incidences are named by their atom and clause/literal presentation indices.
This file supplies the exact bridge: a genuine occurrence is looked up in
its angular-and-radial list, the eight-occurrence bound packages that index as a
slot, and the length-aware terminal profile is proved to contain the
occurrence's classified terminal datum at that slot.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Slot occupied by one genuine occurrence in its atom's angular-and-radial
list. -/
def retainedAngularTerminalSlot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    RetainedTerminalSlot :=
  ⟨(angularOccurrenceVariables source routes atom).idxOf copy, by
    have angularMember :
        copy ∈ angularOccurrenceVariables source routes atom :=
      (angularOccurrenceVariables_perm
        source routes atom).mem_iff.mpr copyMember
    have indexLt :=
      List.idxOf_lt_length_of_mem angularMember
    have lengthLe :
        (angularOccurrenceVariables
          source routes atom).length ≤ 8 := by
      simpa [angularOccurrenceOrder] using fits atom
    omega⟩

@[simp]
theorem retainedAngularTerminalSlot_val
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    (retainedAngularTerminalSlot
      source routes fits atom copy copyMember).val =
        (angularOccurrenceVariables
          source routes atom).idxOf copy :=
  rfl

/-- Looking up the resulting slot in the angular occurrence list recovers
the original occurrence exactly. -/
theorem angularOccurrenceVariables_getElem_retainedAngularTerminalSlot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    (angularOccurrenceVariables
      source routes atom)[
        (retainedAngularTerminalSlot
          source routes fits atom copy copyMember).val]? =
      some copy := by
  have angularMember :
      copy ∈ angularOccurrenceVariables source routes atom :=
    (angularOccurrenceVariables_perm
      source routes atom).mem_iff.mpr copyMember
  simpa [retainedAngularTerminalSlot] using
    List.getElem?_idxOf angularMember

/-- The length-aware profile stores the occurrence's exact classified
terminal datum at its looked-up slot. -/
theorem retainedAngularTerminalProfile_getElem_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    let profile :=
      retainedAngularTerminalProfile
        source routes certificate fits atom
    let slot :=
      retainedAngularTerminalSlot
        source routes fits atom copy copyMember
    profile.terminals[slot.val]? =
      some
        (classifiedRetainedTerminalData
          (occurrenceTerminalVector routes copy)) := by
  dsimp only
  have angularMember :
      copy ∈ angularOccurrenceVariables source routes atom :=
    (angularOccurrenceVariables_perm
      source routes atom).mem_iff.mpr copyMember
  simp [retainedAngularTerminalProfile,
    angularRetainedTerminalData,
    retainedAngularTerminalSlot,
    List.getElem?_idxOf angularMember]

/-- The finite shape records the occurrence's exact classified direction at
its looked-up slot. -/
theorem retainedAngularTerminalProfile_finiteShape_direction_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    let profile :=
      retainedAngularTerminalProfile
        source routes certificate fits atom
    let slot :=
      retainedAngularTerminalSlot
        source routes fits atom copy copyMember
    profile.finiteShape.direction slot =
      some
        (classifiedRetainedTerminalData
          (occurrenceTerminalVector routes copy)).1 := by
  dsimp only
  let profile :=
    retainedAngularTerminalProfile
      source routes certificate fits atom
  let slot :=
    retainedAngularTerminalSlot
      source routes fits atom copy copyMember
  have terminalLookup :=
    retainedAngularTerminalProfile_getElem_slot
      source routes certificate fits atom copy copyMember
  simpa [profile, slot,
    RetainedAngularTerminalProfile.finiteShape]
    using congrArg (Option.map Prod.fst) terminalLookup

/-- Consequently the finite shape selects the exact complete refined fan
route for this occurrence. -/
theorem retainedAngularTerminalProfile_fanRefinedRoute_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    (fits : FitsEightSlots (angularOccurrenceOrder source routes))
    (atom : Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    let profile :=
      retainedAngularTerminalProfile
        source routes certificate fits atom
    let slot :=
      retainedAngularTerminalSlot
        source routes fits atom copy copyMember
    profile.finiteShape.fanRefinedRoute slot =
      some
        (retainedTerminalFanRefinedRoute
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector routes copy)).1
          slot) := by
  dsimp only
  apply
    RetainedAngularTerminalShape.fanRefinedRoute_eq_some
  exact
    retainedAngularTerminalProfile_finiteShape_direction_slot
      source routes certificate fits atom copy copyMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
