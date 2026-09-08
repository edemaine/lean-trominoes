/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FinalFanDataStableProjection
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFans

/-! # A stable fan agrees with the source when its active fields agree -/

noncomputable section

namespace LeanTrominoes.FinalFanDataTripleAssembler

open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

private theorem fan_eq_of_fields (first second : VariableRibbonFanData)
    (count : first.countPred = second.countPred)
    (kind : ∀ slot, first.kind slot = second.kind slot)
    (polarity : ∀ slot, first.polarity slot = second.polarity slot)
    (direction : ∀ slot, first.direction slot = second.direction slot) : first = second := by
  have kinds := funext kind
  have polarities := funext polarity
  have directions := funext direction
  cases first
  cases second
  simp_all only

/-- Agreement at the genuine source slots determines the entire finite fan,
including the shared last-occurrence fallback and unused north directions. -/
theorem stableFan_eq_source_of_fields
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (keys : List Nat) (records : List OccurrenceData) (value : Nat)
    (fields : ∀ slot ∈ usedSlots source.erase entry.1.1,
      let record := FiniteAlphabetKeyedValueLookup.alignedDatum keys records (value * 3 + slot.index)
      ((record.kind, record.polarity), record.direction) =
        (((sourceVariableRibbonFanData presentation entry).kind (occurrenceVariableSiteSlot slot),
          (sourceVariableRibbonFanData presentation entry).polarity (occurrenceVariableSiteSlot slot)),
          (sourceVariableRibbonFanData presentation entry).direction (occurrenceVariableSiteSlot slot))) :
    stableFan keys records value (sourceVariableRibbonCountPred source.erase entry.1.1) =
      sourceVariableRibbonFanData presentation entry := by
  have inactiveDirection (slot : VariableSiteSlot)
      (absent : variableSiteOccurrenceSlot slot ∉ usedSlots source.erase entry.1.1) :
      (sourceVariableRibbonFanData presentation entry).direction slot = .north := by
    have absentEntry : (entry.1.1, variableSiteOccurrenceSlot slot) ∉ occurrenceEntries source.erase := by
      intro member
      exact absent ((mem_occurrenceEntries_iff source.erase entry.1.1 _).mp member).2
    simp only [sourceVariableRibbonFanData, dif_neg absentEntry]
  rcases usedSlots_cases_of_atom_mem source.erase entry.1.1 entry.atom_mem with one | two | three
  ·
    have firstFields := fields .first (by simp [one])
    have firstKind := congrArg (fun fields => fields.1.1) firstFields
    have firstPolarity := congrArg (fun fields => fields.1.2) firstFields
    have firstDirection := congrArg Prod.snd firstFields
    apply fan_eq_of_fields
    · rfl
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using firstKind
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using firstKind
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using firstKind
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using firstPolarity
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using firstPolarity
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using firstPolarity
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            one, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using firstDirection
      | second =>
          rw [stableFan_direction_of_inactive keys records value _ .second (by
            simp [sourceVariableRibbonCountPred, one, VariableSiteSlot.index])]
          exact (inactiveDirection .second (by simp [one, variableSiteOccurrenceSlot])).symm
      | third =>
          rw [stableFan_direction_of_inactive keys records value _ .third (by
            simp [sourceVariableRibbonCountPred, one, VariableSiteSlot.index])]
          exact (inactiveDirection .third (by simp [one, variableSiteOccurrenceSlot])).symm
  ·
    have firstFields := fields .first (by simp [two])
    have firstKind := congrArg (fun fields => fields.1.1) firstFields
    have firstPolarity := congrArg (fun fields => fields.1.2) firstFields
    have firstDirection := congrArg Prod.snd firstFields
    have secondFields := fields .second (by simp [two])
    have secondKind := congrArg (fun fields => fields.1.1) secondFields
    have secondPolarity := congrArg (fun fields => fields.1.2) secondFields
    have secondDirection := congrArg Prod.snd secondFields
    apply fan_eq_of_fields
    · rfl
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using firstKind
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using secondKind
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using secondKind
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using firstPolarity
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using secondPolarity
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using secondPolarity
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using firstDirection
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            two, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using secondDirection
      | third =>
          rw [stableFan_direction_of_inactive keys records value _ .third (by
            simp [sourceVariableRibbonCountPred, two, VariableSiteSlot.index])]
          exact (inactiveDirection .third (by simp [two, variableSiteOccurrenceSlot])).symm
  ·
    have firstFields := fields .first (by simp [three])
    have firstKind := congrArg (fun fields => fields.1.1) firstFields
    have firstPolarity := congrArg (fun fields => fields.1.2) firstFields
    have firstDirection := congrArg Prod.snd firstFields
    have secondFields := fields .second (by simp [three])
    have secondKind := congrArg (fun fields => fields.1.1) secondFields
    have secondPolarity := congrArg (fun fields => fields.1.2) secondFields
    have secondDirection := congrArg Prod.snd secondFields
    have thirdFields := fields .third (by simp [three])
    have thirdKind := congrArg (fun fields => fields.1.1) thirdFields
    have thirdPolarity := congrArg (fun fields => fields.1.2) thirdFields
    have thirdDirection := congrArg Prod.snd thirdFields
    apply fan_eq_of_fields
    · rfl
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using firstKind
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using secondKind
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSiteKind] using thirdKind
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using firstPolarity
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using secondPolarity
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot, sourceVariableRibbonFanData, sourceVariableSitePolarity] using thirdPolarity
    · intro slot
      cases slot with
      | first =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using firstDirection
      | second =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using secondDirection
      | third =>
          simpa [stableFan, stableSelectedOccurrence, fanData, sourceVariableRibbonCountPred,
            three, FinalFanQueryRanks.selectedRank, PeriodicOneInThreeToThreeDM.OccurrenceSlot.index,
            occurrenceVariableSiteSlot] using thirdDirection

end LeanTrominoes.FinalFanDataTripleAssembler

end
