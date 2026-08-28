/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareData
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComparisonComponents

/-! # Structural atom words for global retained occurrences -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Presentation-ordered structural words of all occurrence atoms. -/
def retainedOccurrenceGlobalAtomWords
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool) : DelimitedBinaryWords.Input :=
  ⟨(allOccurrenceVariables source).map fun copy => atomWord copy.1⟩

/-- Structural atom words are equivalently a clausewise flattening in the
ordinary occurrence presentation. -/
theorem retainedOccurrenceGlobalAtomWords_eq_clausewise
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool) :
    (retainedOccurrenceGlobalAtomWords source atomWord).words =
      source.clauses.flatMap fun clause =>
        clause.map fun literal => atomWord literal.atom := by
  unfold retainedOccurrenceGlobalAtomWords
  rw [show
      (allOccurrenceVariables source).map (fun copy => atomWord copy.1) =
        ((allOccurrenceVariables source).map Prod.fst).map atomWord by
      simp only [List.map_map, Function.comp_def]]
  rw [allOccurrenceVariables_fst]
  unfold PeriodicCNF.variableOccurrences
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- Injective structural words turn the generic word-equality square into
the exact global same-atom stream. -/
theorem retainedOccurrenceGlobalAtomEqualityBits_eq_words
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool)
    (atomWordInjective : Function.Injective atomWord) :
    retainedOccurrenceGlobalAtomEqualityBits source =
      DelimitedBinaryWordEqualitySquare.equalityBits
        (retainedOccurrenceGlobalAtomWords source atomWord) := by
  rw [DelimitedBinaryWordEqualitySquare.equalityBits_eq_flatMap]
  unfold retainedOccurrenceGlobalAtomEqualityBits
    retainedOccurrenceGlobalOrderedPairs
    retainedOccurrenceGlobalAtomWords
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
    exact congrArg atomWord equal.symm
  · intro equal
    exact (atomWordInjective equal).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
