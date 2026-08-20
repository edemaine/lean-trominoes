/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAssignmentRecordData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizationInputSemanticBridge

/-! # Proof-free direct sparse normalization assignments -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseComputedAssignmentStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Fully executable horizontal problem-and-drawing data generated from raw
source symbols. -/
def directSparseComputedNormalizationInputOfSymbols
    (symbols : List encoding.Γ) :
    PeriodicThreeDM.NormalizationCompiler.Input :=
  horizontalNormalizationInputComputed
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)

@[simp] theorem directSparseComputedNormalizationInputOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseComputedNormalizationInputOfSymbols decider symbols =
      directSparseNormalizationInputOfSymbols decider symbols := by
  exact horizontalNormalizationInputComputed_eq_normalizationInput _

/-- Assignment list obtained only from executable horizontal data. -/
def directSparseComputedAssignmentsOfSymbols (symbols : List encoding.Γ) :
    List PeriodicThreeDM.NormalizedCellAssignment :=
  PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments
    (directSparseComputedNormalizationInputOfSymbols decider symbols)

@[simp] theorem directSparseComputedAssignmentsOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseComputedAssignmentsOfSymbols decider symbols =
      directSparseAssignmentsOfSymbols decider symbols := by
  rw [directSparseComputedAssignmentsOfSymbols,
    directSparseAssignmentsOfSymbols,
    directSparseComputedNormalizationInputOfSymbols_eq]

/-- Canonical record target stated solely through the executable horizontal
constructor. -/
def directSparseComputedAssignmentRecordsOfSymbols
    (symbols : List encoding.Γ) : List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentsTokens
    (directSparseComputedAssignmentsOfSymbols decider symbols)

@[simp] theorem directSparseComputedAssignmentRecordsOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseComputedAssignmentRecordsOfSymbols decider symbols =
      directSparseAssignmentRecordsOfSymbols decider symbols := by
  rw [directSparseComputedAssignmentRecordsOfSymbols,
    directSparseAssignmentRecordsOfSymbols,
    directSparseComputedAssignmentsOfSymbols_eq]

end PeriodicCNFStripReduction
end LeanTrominoes
