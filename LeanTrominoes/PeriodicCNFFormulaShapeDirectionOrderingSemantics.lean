/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingData
import LeanTrominoes.PeriodicCNFFormulaShapeOfFormulaSemantics

/-! # Semantics of finite direction-aware formula-shape ordering -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeDirectionOrdering

open UnaryProgramClauseProfile

theorem DirectedClauseProfile.orderedLiterals_perm
    (profile : DirectedClauseProfile) :
    profile.orderedLiterals.Perm
      (profile.taggedLiterals.map Prod.fst) := by
  unfold DirectedClauseProfile.orderedLiterals
  exact (List.perm_insertionSort directionLE profile.taggedLiterals).map
    Prod.fst

theorem DirectedClauseProfile.sourceLiterals_nonempty
    (profile : DirectedClauseProfile) :
    profile.taggedLiterals.map Prod.fst ≠ [] := by
  cases profile <;> simp [DirectedClauseProfile.taggedLiterals]

theorem DirectedClauseProfile.sourceLiterals_length_le_three
    (profile : DirectedClauseProfile) :
    (profile.taggedLiterals.map Prod.fst).length ≤ 3 := by
  cases profile <;> simp [DirectedClauseProfile.taggedLiterals]

/-- The total clause-profile repackaging has no fallback behavior on the
finite unary, binary, and ternary direction descriptors. -/
@[simp] theorem DirectedClauseProfile.orderedProfile_literals
    (profile : DirectedClauseProfile) :
    profile.orderedProfile.literals = profile.orderedLiterals := by
  apply FormulaShapeOfFormula.clauseProfile_literals
  · apply List.ne_nil_of_length_pos
    rw [profile.orderedLiterals_perm.length_eq]
    exact List.length_pos_iff.mpr profile.sourceLiterals_nonempty
  · rw [profile.orderedLiterals_perm.length_eq]
    exact profile.sourceLiterals_length_le_three

@[simp] theorem clauseProfiles_tokenBlock (token : Token) :
    FormulaShape.clauseProfiles (tokenBlock token) =
      match token with
      | .clause profile => [profile.orderedProfile]
      | .variable => [] := by
  cases token <;> rfl

/-- The compiled ordinary shape contains exactly one stably ordered profile
per annotated clause, in source clause order. -/
@[simp] theorem clauseProfiles_shape (source : List Token) :
    FormulaShape.clauseProfiles (shape source) =
      source.filterMap fun
        | .clause profile => some profile.orderedProfile
        | .variable => none := by
  unfold shape
  induction source with
  | nil => rfl
  | cons token source induction =>
      rw [List.flatMap_cons, FormulaShape.clauseProfiles_append,
        clauseProfiles_tokenBlock]
      cases token <;> simp [induction]

end FormulaShapeDirectionOrdering
end PeriodicCNF
end LeanTrominoes
