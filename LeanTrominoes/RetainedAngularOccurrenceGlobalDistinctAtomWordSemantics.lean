/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.RetainedAngularOccurrenceGlobalSeparatedAtomWordSemantics

/-! # Distinct represented occurrence-atom words -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Deduplicating a separating presentation-ordered atom-word column gives
the stable distinct-atom order, with the word map applied afterward. -/
theorem retainedOccurrenceGlobalAtomWords_dedup_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atomWord : Variable → List Bool)
    (separates : OccurrenceAtomWordsSeparate source atomWord) :
    (retainedOccurrenceGlobalAtomWords source atomWord).words.dedup =
      source.variableOccurrences.dedup.map atomWord := by
  unfold retainedOccurrenceGlobalAtomWords
  rw [show
    (allOccurrenceVariables source).map (fun copy => atomWord copy.1) =
      ((allOccurrenceVariables source).map Prod.fst).map atomWord by
    simp only [List.map_map, Function.comp_def]]
  rw [allOccurrenceVariables_fst]
  exact List.dedup_map_of_injective_on atomWord
    source.variableOccurrences separates

end LeanTrominoes.PeriodicEightOccurrenceSplit
