/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Semantics of retained terminal-coordinate components -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace TerminalCoordinateComponents

open PeriodicThreeSATThree

private theorem strictLowerBits_directionRanks
    (values : List (Nat × Nat)) :
    UnaryFieldStrictLowerRows.strictLowerBits (directionRanks values) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (second.1 < first.1) := by
  rw [UnaryFieldStrictLowerRows.strictLowerBits_eq_flatMap]
  unfold directionRanks SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def]

private theorem strictLowerBits_radialLengths
    (values : List (Nat × Nat)) :
    UnaryFieldStrictLowerRows.strictLowerBits (radialLengths values) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (second.2 < first.2) := by
  rw [UnaryFieldStrictLowerRows.strictLowerBits_eq_flatMap]
  unfold radialLengths SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def]

private theorem equalityBits_directionRanks
    (values : List (Nat × Nat)) :
    UnaryFieldEqualityRows.equalityBits (directionRanks values) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (first.1 = second.1) := by
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold directionRanks SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def]

private theorem equalityBits_radialLengths
    (values : List (Nat × Nat)) :
    UnaryFieldEqualityRows.equalityBits (radialLengths values) =
      SignedUnaryStrictLower.matrix values fun first second =>
        decide (first.2 = second.2) := by
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold radialLengths SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro first _firstMember
  simp [List.map_map, Function.comp_def]

/-- The numeric component formula is exactly target-major strict
lexicographic comparison. -/
theorem strictLowerBits_eq_flatMap (values : List (Nat × Nat)) :
    strictLowerBits values =
      values.flatMap fun target =>
        values.map fun candidate =>
          decide (toLex candidate < toLex target) := by
  unfold strictLowerBits
  rw [strictLowerBits_directionRanks,
    equalityBits_directionRanks,
    strictLowerBits_radialLengths]
  rw [SignedUnaryStrictLower.pairwise_matrix,
    SignedUnaryStrictLower.pairwise_matrix]
  unfold SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  apply List.flatMap_congr
  intro target _targetMember
  apply List.map_congr_left
  intro candidate _candidateMember
  apply Bool.eq_iff_iff.mpr
  simp only [UnarySmallSumBooleans.Operation.apply,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Prod.Lex.toLex_lt_toLex]
  constructor
  · intro condition
    rcases condition with lower | ⟨equal, lower⟩
    · exact Or.inl lower
    · exact Or.inr ⟨equal.symm, lower⟩
  · intro condition
    rcases condition with lower | ⟨equal, lower⟩
    · exact Or.inl lower
    · exact Or.inr ⟨equal.symm, lower⟩

/-- The numeric component formula is exactly target-major coordinate
equality. -/
theorem equalityBits_eq_flatMap (values : List (Nat × Nat)) :
    equalityBits values =
      values.flatMap fun target =>
        values.map fun candidate =>
          decide (toLex candidate = toLex target) := by
  unfold equalityBits
  rw [equalityBits_directionRanks,
    equalityBits_radialLengths]
  rw [SignedUnaryStrictLower.pairwise_matrix]
  unfold SignedUnaryStrictLower.matrix
    SignedUnaryStrictLower.matrixRows
  apply List.flatMap_congr
  intro target _targetMember
  apply List.map_congr_left
  intro candidate _candidateMember
  apply Bool.eq_iff_iff.mpr
  simp only [UnarySmallSumBooleans.Operation.apply,
    Bool.and_eq_true, decide_eq_true_eq, toLex_inj]
  constructor
  · intro equalComponents
    apply Prod.ext
    · exact equalComponents.1.symm
    · exact equalComponents.2.symm
  · intro equal
    subst target
    exact ⟨rfl, rfl⟩

/-- Consequently the actual global strict terminal-coordinate stream is
exactly the component pipeline on the presentation-ordered coordinates. -/
theorem retainedOccurrenceGlobalTerminalStrictLowerBits_eq_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalTerminalStrictLowerBits source routes =
      strictLowerBits (coordinates source routes) := by
  rw [strictLowerBits_eq_flatMap]
  unfold retainedOccurrenceGlobalTerminalStrictLowerBits
    retainedOccurrenceGlobalOrderedPairs coordinates
  dsimp only
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro target _targetMember
  simp [List.map_map, Function.comp_def]

/-- Likewise the actual global terminal-coordinate equality stream is the
componentwise equality pipeline. -/
theorem retainedOccurrenceGlobalTerminalEqualityBits_eq_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    retainedOccurrenceGlobalTerminalEqualityBits source routes =
      equalityBits (coordinates source routes) := by
  rw [equalityBits_eq_flatMap]
  unfold retainedOccurrenceGlobalTerminalEqualityBits
    retainedOccurrenceGlobalOrderedPairs coordinates
  dsimp only
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro target _targetMember
  simp [List.map_map, Function.comp_def]

end TerminalCoordinateComponents
end PeriodicEightOccurrenceSplit
end LeanTrominoes
