/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrences

/-! # Source occurrence groups used by cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Positional occurrence copies grouped in source-variable order. -/
def cycleLinkOccurrenceGroups
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List (List (ThreeOccurrenceVariable Variable)) :=
  (sourceVariables source).map (occurrenceVariables source)

/-- Distinct source variables have disjoint positional-copy groups. -/
theorem cycleLinkOccurrenceGroups_flatten_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (cycleLinkOccurrenceGroups source).flatten.Nodup := by
  change ((sourceVariables source).flatMap
    (occurrenceVariables source)).Nodup
  rw [List.nodup_flatMap]
  constructor
  · intro atom _atomMember
    exact occurrenceVariables_nodup source atom
  · have variablesNodup : (sourceVariables source).Nodup := by
      unfold sourceVariables
      exact List.nodup_dedup _
    refine variablesNodup.imp ?_
    intro first second different
    change List.Disjoint (occurrenceVariables source first)
      (occurrenceVariables source second)
    rw [List.disjoint_left]
    intro copy firstMember secondMember
    have firstEq := occurrenceVariables_fst source first firstMember
    have secondEq := occurrenceVariables_fst source second secondMember
    exact different (firstEq.symm.trans secondEq)

end PeriodicThreeSATThree
end LeanTrominoes
