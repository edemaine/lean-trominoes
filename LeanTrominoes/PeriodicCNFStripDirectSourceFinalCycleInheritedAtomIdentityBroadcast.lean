/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockIndexLookupSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedAtomIdentitySemantics

/-! # Blockwise semantics of inherited cycle identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The retained-variable marker list is a repeated variable token whose
length is the aligned distinct-identity count. -/
theorem directRetainedFigureNineFiniteSourceVariableMarkers_eq_replicate_identities
    (symbols : List encoding.Γ) :
    directRetainedFigureNineFiniteSourceVariableMarkers decider symbols =
      List.replicate
        (directSourceFinalDistinctAtomIdentityIndices
          decider symbols).length
        FormulaShapeDirectionOrdering.Token.variable := by
  have lengthEq :=
    directSourceFinalDistinctAtomIdentityIndices_length_eq_markers
      decider symbols
  unfold directRetainedFigureNineFiniteSourceVariableMarkers at lengthEq ⊢
  simp only [List.length_replicate] at lengthEq
  rw [lengthEq]

/-- The compiled cycle lookup repeats each distinct retained-source identity
across exactly one complete implication-cycle occurrence block. -/
theorem directSourceFinalCycleInheritedAtomIdentityIndices_eq_flatMap_replicate
    (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedAtomIdentityIndices decider symbols =
      (directSourceFinalDistinctAtomIdentityIndices decider symbols).flatMap
        fun identity => List.replicate
          (directSourceFinalCycleOccurrenceBlockLength
            FormulaShapeDirectionOrdering.Token.variable)
          identity := by
  rw [directSourceFinalCycleInheritedAtomIdentityIndices_eq_map_getD,
    directSourceFinalCycleMarkerIndexQueries_eq_expected]
  rw [FiniteBlockIndices.expected_lookup_eq_broadcastValues]
  · rw [directRetainedFigureNineFiniteSourceVariableMarkers_eq_replicate_identities,
      FiniteBlockIndices.broadcastValues_replicate]
  · exact (directSourceFinalDistinctAtomIdentityIndices_length_eq_markers
      decider symbols).symm
  · intro token tokenMember
    have tokenEq : token =
        FormulaShapeDirectionOrdering.Token.variable := by
      rw [directRetainedFigureNineFiniteSourceVariableMarkers_eq_replicate_identities]
        at tokenMember
      exact List.eq_of_mem_replicate tokenMember
    subst token
    native_decide

end LeanTrominoes.PeriodicCNFStripReduction
