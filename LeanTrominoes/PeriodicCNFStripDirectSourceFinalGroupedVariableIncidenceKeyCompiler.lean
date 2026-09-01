/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Consecutive keys for grouped variable incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGroupedVariableIncidenceKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- One zero-valued unary field per grouped variable incidence. -/
def directSourceFinalGroupedVariableIncidenceKeySeeds
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values (fun _ :
      HorizontalFiniteIncidenceDirectionQuery => 0)
    (directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols)

/-- Consecutive global keys `0, ..., n - 1` for all grouped variable
incidences in their prefix-query order. -/
def directSourceFinalGroupedVariableIncidenceKeys
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldRange.values
    (directSourceFinalGroupedVariableIncidenceKeySeeds decider symbols)

noncomputable def
    directSourceFinalGroupedVariableIncidenceKeySeedsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableIncidenceKeySeeds decider) := by
  unfold directSourceFinalGroupedVariableIncidenceKeySeeds
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableIncidencePrefixQueriesComputableInPolyTime
      decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      fun _ : HorizontalFiniteIncidenceDirectionQuery => 0)

/-- Consecutive incidence keys compile in polynomial time from the finite
query stream. -/
noncomputable def
    directSourceFinalGroupedVariableIncidenceKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalGroupedVariableIncidenceKeys decider) := by
  unfold directSourceFinalGroupedVariableIncidenceKeys
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGroupedVariableIncidenceKeySeedsComputableInPolyTime
      decider)
    UnaryFieldRange.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
