/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Consecutive keys for the complete canonical incidence stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalIncidenceKeyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The finite queries underlying the canonical incidence stream, in the
same variable-prefix/clause-suffix order as its direction blocks. -/
def directSourceFinalCanonicalIncidenceQueries
    (symbols : List encoding.Γ) :
    List HorizontalFiniteIncidenceDirectionQuery :=
  directSourceFinalGroupedVariableIncidencePrefixQueries decider symbols ++
    directSourceFinalClauseIncidenceQueries decider symbols

/-- One zero-valued field per canonical incidence block. -/
def directSourceFinalCanonicalIncidenceKeySeeds
    (symbols : List encoding.Γ) : List Nat :=
  FiniteUnaryFieldMap.values
    (fun _ : HorizontalFiniteIncidenceDirectionQuery => 0)
    (directSourceFinalCanonicalIncidenceQueries decider symbols)

/-- Consecutive keys for every canonical incidence block. -/
def directSourceFinalCanonicalIncidenceKeys
    (symbols : List encoding.Γ) : List Nat :=
  UnaryFieldRange.values
    (directSourceFinalCanonicalIncidenceKeySeeds decider symbols)

noncomputable def
    directSourceFinalCanonicalIncidenceQueriesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCanonicalIncidenceQueries decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCanonicalIncidenceQueries
    exact TM2ListAppend.computableInPolyTime
      (directSourceFinalGroupedVariableIncidencePrefixQueriesComputableInPolyTime
        decider)
      (directSourceFinalClauseIncidenceQueriesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

noncomputable def
    directSourceFinalCanonicalIncidenceKeySeedsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalIncidenceKeySeeds decider) := by
  unfold directSourceFinalCanonicalIncidenceKeySeeds
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalIncidenceQueriesComputableInPolyTime decider)
    (FiniteUnaryFieldMap.computableInPolyTime
      fun _ : HorizontalFiniteIncidenceDirectionQuery => 0)

/-- The complete canonical incidence-key column compiles in polynomial
time from the same finite query stream as the direction blocks. -/
noncomputable def
    directSourceFinalCanonicalIncidenceKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalIncidenceKeys decider) := by
  unfold directSourceFinalCanonicalIncidenceKeys
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalIncidenceKeySeedsComputableInPolyTime decider)
    UnaryFieldRange.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
