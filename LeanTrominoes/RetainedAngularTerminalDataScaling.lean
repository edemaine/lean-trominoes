/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedTerminalScaling

/-!
# Scaling retained angular terminal profiles

Positive integral refinement changes physical coordinates but not the
polar-and-radial order of incidence occurrences.  This file lifts the
pointwise retained-terminal scaling theorems across the actual angular
occurrence list and across the compact local profile consumed by the
fixed-eight adapter.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Scaling an incidence route scales the backwards terminal vector of each
syntactic occurrence by the same factor. -/
@[simp]
theorem occurrenceTerminalVector_scaleIncidenceRoutes
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {Variable : Type*}
    (copy : ThreeOccurrenceVariable Variable) :
    occurrenceTerminalVector
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor routes)
        copy =
      Cell.scale factor
        (occurrenceTerminalVector routes copy) := by
  simp [occurrenceTerminalVector,
    PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
    routeTerminalVector_scalePolyline]

/-- Positive uniform scaling leaves the occurrence-angle comparator
unchanged. -/
theorem occurrenceAngleLE_scaleIncidenceRoutes
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {Variable : Type*}
    (first second : ThreeOccurrenceVariable Variable) :
    occurrenceAngleLE
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor routes)
        first second =
      occurrenceAngleLE routes first second := by
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  simp [occurrenceAngleLE,
    terminalVectorAngleRadialLE_uniform_scale
      factorPositiveInt]

/-- Angular sorting, including its radial tie-break, returns the identical
occurrence list after positive uniform scaling. -/
theorem angularOccurrenceVariables_scaleIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    angularOccurrenceVariables source
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor routes)
        atom =
      angularOccurrenceVariables source routes atom := by
  unfold angularOccurrenceVariables
  congr 1
  funext first second
  exact
    occurrenceAngleLE_scaleIncidenceRoutes
      factorPositive routes first second

/-- Positive uniform scaling leaves the complete per-variable angular
occurrence order unchanged. -/
theorem angularOccurrenceOrder_scaleIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    angularOccurrenceOrder source
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) =
      angularOccurrenceOrder source routes := by
  unfold angularOccurrenceOrder
  congr 1
  funext atom
  exact
    angularOccurrenceVariables_scaleIncidenceRoutes
      source factorPositive routes atom

/-- The total terminal-data projection scales exactly whenever its source
classification is certified. -/
theorem classifiedRetainedTerminalData_scale_of_classified
    {factor : Nat} (factorPositive : 0 < factor)
    {vector : Cell}
    {terminal : RetainedTerminalData}
    (classified :
      retainedTerminalDirectionClassify vector =
        some terminal) :
    classifiedRetainedTerminalData
        (Cell.scale factor vector) =
      scaleRetainedTerminalData factor
        (classifiedRetainedTerminalData vector) := by
  rw [classifiedRetainedTerminalData_eq_of_classified
    classified]
  rw [classifiedRetainedTerminalData_eq_of_classified
    (retainedTerminalDirectionClassify_scale
      factorPositive classified)]
  rfl

/-- Scaling every route maps the entire length-aware angular list by the
finite terminal-data scaling operation. -/
theorem angularRetainedTerminalData_scaleIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    {factor : Nat} (factorPositive : 0 < factor)
    (atom : Variable) :
    angularRetainedTerminalData source
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          factor routes)
        atom =
      (angularRetainedTerminalData
        source routes atom).map
          (scaleRetainedTerminalData factor) := by
  rw [angularRetainedTerminalData,
    angularOccurrenceVariables_scaleIncidenceRoutes
      source factorPositive routes atom,
    angularRetainedTerminalData, List.map_map]
  apply List.map_congr_left
  intro copy copyMember
  have occurrenceMember :
      copy ∈ occurrenceVariables source atom :=
    (angularOccurrenceVariables_perm
      source routes atom).mem_iff.mp copyMember
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (occurrenceTerminalVector routes copy)).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff _).2
      (certificate atom copy occurrenceMember)
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  rw [occurrenceTerminalVector_scaleIncidenceRoutes]
  exact
    classifiedRetainedTerminalData_scale_of_classified
      factorPositive classified

/-- Positive uniform scaling preserves the retained-terminal certificate for
every syntactic occurrence. -/
theorem RetainedOccurrenceTerminalCertificate.scaleIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {routes : PositionedPeriodicCNF.IncidenceRoutes}
    (certificate :
      RetainedOccurrenceTerminalCertificate source routes)
    {factor : Nat} (factorPositive : 0 < factor) :
    RetainedOccurrenceTerminalCertificate source
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes) := by
  intro atom copy copyMember
  have retained :=
    certificate atom copy copyMember
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (occurrenceTerminalVector routes copy)).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff _).2 retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  apply
    (retainedTerminalDirectionClassify_isSome_iff _).1
  rw [occurrenceTerminalVector_scaleIncidenceRoutes]
  exact
    Option.isSome_iff_exists.mpr
      ⟨scaleRetainedTerminalData factor terminal,
        retainedTerminalDirectionClassify_scale
          factorPositive classified⟩

/-- Scale every terminal in a compact local profile. -/
def RetainedAngularTerminalProfile.scale
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor) :
    RetainedAngularTerminalProfile where
  terminals :=
    profile.terminals.map
      (scaleRetainedTerminalData factor)
  rankSorted := by
    rw [List.pairwise_map]
    simpa using profile.rankSorted
  tiesRadiallySorted := by
    rw [List.pairwise_map]
    exact profile.tiesRadiallySorted.imp fun
      ordered directionsEqual => by
        simpa only [scaleRetainedTerminalData_length] using
          Nat.mul_le_mul_left factor
            (ordered (by
              simpa only [scaleRetainedTerminalData_direction]
                using directionsEqual))
  lengthsPositive := by
    intro terminal terminalMember
    rcases List.mem_map.mp terminalMember with
      ⟨sourceTerminal, sourceMember, rfl⟩
    exact
      scaleRetainedTerminalData_length_pos
        factorPositive
        (profile.lengthsPositive
          sourceTerminal sourceMember)
  fitsEight := by
    simpa using profile.fitsEight

@[simp]
theorem RetainedAngularTerminalProfile.scale_terminals
    (profile : RetainedAngularTerminalProfile)
    (factor : Nat) (factorPositive : 0 < factor) :
    (profile.scale factor factorPositive).terminals =
      profile.terminals.map
        (scaleRetainedTerminalData factor) :=
  rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
