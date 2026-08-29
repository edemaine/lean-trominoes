/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteEncodingNativeFields
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseOccurrenceRoleCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGlobalTerminalSlotCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Unary fields for final occurrence roles and slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoleSlotFieldStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoleSlotFieldVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Reserve one disjoint eight-value block for every finite occurrence role. -/
def directSourceFinalOccurrenceRoleBase
    (role : RetainedFinalCopiedClauseOccurrenceRole) : Nat :=
  8 * FiniteEncodingNativeFields.symbolIndex role

def directSourceFinalOccurrenceRoleBaseValues
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values directSourceFinalOccurrenceRoleBase
    (retainedFinalCopiedClauseOccurrenceRoles
      (directRetainedFinalClauseQueryAssembly decider symbols))

def directSourceFinalTerminalSlotValues
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values Fin.val
    (BoundedRetainedTerminalSlots.slots
      (retainedOccurrenceGlobalStableTerminalRanks
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes
          (directSourceFormula decider symbols))))

/-- The final occurrence roles compile to their block-aligned unary bases. -/
noncomputable def
    directSourceFinalOccurrenceRoleBaseValuesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalOccurrenceRoleBaseValues decider) := by
  unfold directSourceFinalOccurrenceRoleBaseValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseOccurrenceRolesComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      directSourceFinalOccurrenceRoleBase)

/-- The final bounded terminal slots compile to their unary values. -/
noncomputable def
    directSourceFinalTerminalSlotValuesComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List Nat)
      encoding.Γ UnaryFieldEncoderMachine.Symbol
      id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalSlotValues decider) := by
  unfold directSourceFinalTerminalSlotValues
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGlobalTerminalSlotsComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime Fin.val)

end LeanTrominoes.PeriodicCNFStripReduction

end
