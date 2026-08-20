/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseComputedAssignmentData

/-! # Vertex/route split of direct sparse assignment records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseComputedRecordSplitStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Canonical records of normalized contracted vertices. -/
def directSparseComputedVertexRecordsOfSymbols
    (symbols : List encoding.Γ) : List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentsTokens
    (PeriodicThreeDM.NormalizationCompiler.finalStripVertexAssignments
      (directSparseComputedNormalizationInputOfSymbols decider symbols))

/-- Canonical records of all normalized route interiors. -/
def directSparseComputedRouteRecordsOfSymbols
    (symbols : List encoding.Γ) : List GadgetSparseAssignmentTokens.Token :=
  GadgetSparseAssignmentTokens.assignmentsTokens
    (PeriodicThreeDM.NormalizationCompiler.finalStripRouteAssignments
      (directSparseComputedNormalizationInputOfSymbols decider symbols))

/-- The complete proof-free record word is exactly its vertex prefix followed
by its route-interior suffix. -/
@[simp] theorem directSparseComputedAssignmentRecordsOfSymbols_eq_split
    (symbols : List encoding.Γ) :
    directSparseComputedAssignmentRecordsOfSymbols decider symbols =
      directSparseComputedVertexRecordsOfSymbols decider symbols ++
        directSparseComputedRouteRecordsOfSymbols decider symbols := by
  unfold directSparseComputedAssignmentRecordsOfSymbols
    directSparseComputedAssignmentsOfSymbols
    PeriodicThreeDM.NormalizationCompiler.finalStripCellAssignments
    directSparseComputedVertexRecordsOfSymbols
    directSparseComputedRouteRecordsOfSymbols
  rw [GadgetSparseAssignmentTokens.assignmentsTokens_append]

end PeriodicCNFStripReduction
end LeanTrominoes
