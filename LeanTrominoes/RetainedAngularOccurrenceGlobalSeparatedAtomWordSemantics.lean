/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalAtomWordSemantics

/-! # Atom words separating only represented occurrence atoms -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- A word function need only separate atoms represented in the finite source
formula in order to decide equality throughout its occurrence square. -/
def OccurrenceAtomWordsSeparate
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool) : Prop :=
  ∀ first ∈ source.variableOccurrences,
    ∀ second ∈ source.variableOccurrences,
      atomWord first = atomWord second → first = second

/-- Separation on represented atoms is sufficient to turn the generic word
equality square into the exact semantic same-atom square. -/
theorem retainedOccurrenceGlobalAtomEqualityBits_eq_separatingWords
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool)
    (separates : OccurrenceAtomWordsSeparate source atomWord) :
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
  intro target targetMember
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro candidate candidateMember
  have targetAtomMember : target.1 ∈ source.variableOccurrences := by
    rw [← allOccurrenceVariables_fst]
    exact List.mem_map.mpr ⟨target, targetMember, rfl⟩
  have candidateAtomMember : candidate.1 ∈ source.variableOccurrences := by
    rw [← allOccurrenceVariables_fst]
    exact List.mem_map.mpr ⟨candidate, candidateMember, rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq]
  constructor
  · intro equal
    exact congrArg atomWord equal.symm
  · intro equal
    exact (separates target.1 targetAtomMember
      candidate.1 candidateAtomMember equal).symm

end PeriodicEightOccurrenceSplit
end LeanTrominoes
