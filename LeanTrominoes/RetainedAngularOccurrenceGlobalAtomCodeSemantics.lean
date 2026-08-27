/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComparisonComponents
import LeanTrominoes.UnaryFieldEqualityRowsCompiler

/-! # Numeric atom codes for global retained occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Presentation-ordered numeric codes of all occurrence atoms. -/
def retainedOccurrenceGlobalAtomCodes
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (atomCode : Variable → Nat) : List Nat :=
  (allOccurrenceVariables source).map fun copy =>
    atomCode copy.1

/-- Any injective numeric atom coding turns the existing unary equality
square into the exact global same-atom stream. -/
theorem retainedOccurrenceGlobalAtomEqualityBits_eq_codes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomCode : Variable → Nat)
    (atomCodeInjective : Function.Injective atomCode) :
    retainedOccurrenceGlobalAtomEqualityBits source =
      UnaryFieldEqualityRows.equalityBits
        (retainedOccurrenceGlobalAtomCodes source atomCode) := by
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  unfold retainedOccurrenceGlobalAtomEqualityBits
    retainedOccurrenceGlobalOrderedPairs
    retainedOccurrenceGlobalAtomCodes
  dsimp only
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro target _targetMember
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro candidate _candidateMember
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · intro equal
    exact congrArg atomCode equal.symm
  · intro equal
    exact (atomCodeInjective equal).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
