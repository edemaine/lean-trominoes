/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceElementCodeCompiler
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Semantics of final clause-incidence element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseIncidenceSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The clause-position compiler emits the literal range of the actual
final-clause fan length. -/
theorem directSourceFinalClauseIncidenceIndices_eq_range
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceIndices decider symbols =
      List.range (directSourceFinalClauseFans decider symbols).length := by
  unfold directSourceFinalClauseIncidenceIndices
    directSourceFinalClauseIncidenceIndexPlaceholders
    UnaryFieldRange.values FiniteUnaryFieldMap.values
  simp

/-- The tag compiler is the direct final-clause-wise expansion of the finite
clause reference table. -/
theorem directSourceFinalClauseIncidenceElementTags_eq_flatMap
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceElementTags decider symbols =
      (directSourceFinalClauseFans decider symbols).flatMap
        finalClauseIncidenceElementTagBlock := by
  rfl

/-- Aligned addition appends each clause-reference tag to its repeated
stride-scaled parent index. -/
theorem directSourceFinalClauseIncidenceElementCodes_eq_zipWith
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncidenceElementCodes decider symbols =
      List.zipWith (fun base tag => base + tag)
        (directSourceFinalClauseIncidenceElementCodeBases
          (directSourceFinalClauseIncidenceIndices decider symbols))
        (directSourceFinalClauseIncidenceElementTags decider symbols) := by
  unfold directSourceFinalClauseIncidenceElementCodes
    AlignedUnaryListClosure.added
  apply UnaryAlignedAddMachine.sums_eq_zipWith
  exact UnaryAlignedAddMachine.Valid.of_length_eq (by simp)

/-- The compiled code column has exactly one entry per final clause-core
incidence query. -/
@[simp] theorem directSourceFinalClauseIncidenceElementCodes_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceElementCodes decider symbols).length =
      (directSourceFinalClauseIncidenceQueries decider symbols).length := by
  rw [directSourceFinalClauseIncidenceElementCodes_eq_zipWith,
    List.length_zipWith]
  simp [directSourceFinalClauseIncidenceQueries,
    finalClauseIncidenceQueryBlock, allClauseSets, Nat.mul_comm]

end LeanTrominoes.PeriodicCNFStripReduction

end
