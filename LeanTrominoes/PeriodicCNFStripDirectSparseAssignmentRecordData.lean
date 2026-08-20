/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseAssignmentTokens
import LeanTrominoes.PeriodicCNFStripDirectSparsePreparedTokenData

/-! # Direct sparse assignment-record stream -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAssignmentRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical finite unary records for all nonblank normalized assignments. -/
def directSparseAssignmentRecordsOfSymbols (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentsTokens
    (directSparseAssignmentsOfSymbols decider symbols)

@[simp] theorem expand_directSparseAssignmentRecordsOfSymbols
    (tromino : Tromino) (symbols : List encoding.Γ) :
    GadgetSparseAssignmentTokens.expand tromino
        (directSparseAssignmentRecordsOfSymbols decider symbols) =
      GadgetSparseExpandedMotifFiniteTokens.preparedSparseExpandedMotif
        tromino (directSparseAssignmentsOfSymbols decider symbols) := by
  exact GadgetSparseAssignmentTokens.expand_assignmentsTokens tromino _

/-- The complete prepared strip stream is the independently verified header
followed by fixed expansion of the canonical assignment records. -/
theorem directSparseCompiledTrominoStripPreparedTokensOfSymbols_eq_records
    (tromino : Tromino) (symbols : List encoding.Γ) :
    directSparseCompiledTrominoStripPreparedTokensOfSymbols
        decider tromino symbols =
      directPreparedHeaderOfSymbols decider symbols ++
        GadgetSparseAssignmentTokens.expand tromino
          (directSparseAssignmentRecordsOfSymbols decider symbols) := by
  unfold directSparseCompiledTrominoStripPreparedTokensOfSymbols
  rw [expand_directSparseAssignmentRecordsOfSymbols]

end PeriodicCNFStripReduction
end LeanTrominoes
