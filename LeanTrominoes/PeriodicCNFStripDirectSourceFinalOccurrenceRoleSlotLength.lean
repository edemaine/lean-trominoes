/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedClauseDescriptorArity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotFieldCompilers
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankLength
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseOccurrenceRoleSemantics

/-! # Alignment of final copied-clause occurrence roles and slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoleSlotLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoleSlotLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled role bases and bounded slot values have exactly matching
field counts, one per final copied occurrence. -/
theorem directSourceFinalOccurrenceRoleBaseValues_length_eq_slots
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceRoleBaseValues decider symbols).length =
      (directSourceFinalTerminalSlotValues decider symbols).length := by
  unfold directSourceFinalOccurrenceRoleBaseValues
    directSourceFinalTerminalSlotValues FiniteUnaryFieldMap.values
    BoundedRetainedTerminalSlots.slots
  simp only [List.length_map]
  rw [show
    (retainedFinalCopiedClauseOccurrenceRoles
      (directRetainedFinalClauseQueryAssembly decider symbols)).length =
      ((directRetainedFinalClauseDescriptorAssembly
        decider symbols).map retainedFinalCopiedDescriptorArity).sum by
    exact retainedFinalCopiedClauseOccurrenceRoles_length _]
  rw [directRetainedFinalClauseDescriptorAssembly_eq_copiedClauseDescriptors]
  rw [directSourceFinalCopiedClauseDescriptorAritySum_eq]
  rw [retainedOccurrenceGlobalStableTerminalRanks_length]
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]

end LeanTrominoes.PeriodicCNFStripReduction

end
