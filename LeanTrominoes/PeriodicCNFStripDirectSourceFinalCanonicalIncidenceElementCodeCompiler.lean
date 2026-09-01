/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeCompiler
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Complete canonical final incidence element-code column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCanonicalIncidenceElementCodeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Complete incidence element identities in the same stable order as the
canonical direction blocks: grouped variable incidences, then clause-core
incidences. -/
def directSourceFinalCanonicalIncidenceElementCodes
    (symbols : List encoding.Γ) : List Nat :=
  directSourceFinalVariableIncidenceElementCodes decider symbols ++
    directSourceFinalClauseIncidenceElementCodes decider symbols

/-- The complete canonical incidence element-code column compiles in
polynomial time. -/
noncomputable def
    directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCanonicalIncidenceElementCodes decider) := by
  unfold directSourceFinalCanonicalIncidenceElementCodes
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalVariableIncidenceElementCodesComputableInPolyTime
      decider)
    (directSourceFinalClauseIncidenceElementCodesComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
