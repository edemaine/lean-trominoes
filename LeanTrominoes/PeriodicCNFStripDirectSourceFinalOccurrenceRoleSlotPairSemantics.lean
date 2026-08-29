/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceRoleSlotPairCompiler
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotDecoderListSemantics

/-! # Semantics of final occurrence-role/slot pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoleSlotPairSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoleSlotPairSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled and decoded stream pairs every final copied occurrence role
with its presentation-aligned bounded global stable-terminal slot. -/
theorem directSourceFinalOccurrenceRoleSlotPairs_eq_zip
    (symbols : List encoding.Γ) :
    directSourceFinalOccurrenceRoleSlotPairs decider symbols =
      List.zip
        (retainedFinalCopiedClauseOccurrenceRoles
          (directRetainedFinalClauseQueryAssembly decider symbols))
        (BoundedRetainedTerminalSlots.slots
          (retainedOccurrenceGlobalStableTerminalRanks
            (retainedFinalCoordinatedScaledSource
              (directSourceFormula decider symbols)).erase
            (retainedFinalCoordinatedScaledSourceRoutes
              (directSourceFormula decider symbols)))) := by
  have lengthEq :=
    directSourceFinalOccurrenceRoleBaseValues_length_eq_slots
      decider symbols
  unfold directSourceFinalOccurrenceRoleBaseValues
    directSourceFinalTerminalSlotValues FiniteUnaryFieldMap.values at lengthEq
  simp only [List.length_map] at lengthEq
  unfold directSourceFinalOccurrenceRoleSlotPairs
    directSourceFinalOccurrenceRoleSlotCodes
    AlignedUnaryListClosure.added
    directSourceFinalOccurrenceRoleBaseValues
    directSourceFinalTerminalSlotValues
    FiniteUnaryFieldMap.values
    directSourceFinalOccurrenceRoleBase
  exact
    FinalOccurrenceRoleSlotDecoder.pairs_sums_roleBases_slotValues
      _ _ lengthEq

end LeanTrominoes.PeriodicCNFStripReduction

end
