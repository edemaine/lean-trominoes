/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleExactOccurrences
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount

/-! # Exact occurrence count after periodic occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Every variable retained by occurrence splitting appears exactly once in
the copied source clauses and twice in its implication cycle. -/
theorem formula_variableOccurrences_count_eq_three_of_mem
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (copy : ThreeOccurrenceVariable Variable)
    (copyMember :
      copy ∈ (PeriodicCNF.variableOccurrences (formula source)).dedup) :
    (PeriodicCNF.variableOccurrences (formula source)).count copy = 3 := by
  have copyFormulaMember :
      copy ∈ PeriodicCNF.variableOccurrences (formula source) :=
    List.mem_dedup.mp copyMember
  have formulaOccurrences :
      PeriodicCNF.variableOccurrences (formula source) =
        allOccurrenceVariables source ++
          PeriodicCNF.variableOccurrences
            (PeriodicCNF.mk (allCycleClauses source)) := by
    unfold formula
    rw [variableOccurrences_append,
      occurrenceClauses_variableOccurrences]
  have copyOriginal : copy ∈ allOccurrenceVariables source := by
    rw [formulaOccurrences, List.mem_append] at copyFormulaMember
    rcases copyFormulaMember with originalMember | cycleMember
    · exact originalMember
    · exact allCycleClauses_variableOccurrences_subset
        source cycleMember
  have sourceCount :
      (allOccurrenceVariables source).count copy = 1 :=
    List.count_eq_one_of_mem
      (allOccurrenceVariables_nodup source) copyOriginal
  have cycleCount :
      (PeriodicCNF.variableOccurrences
        (PeriodicCNF.mk (allCycleClauses source))).count copy = 2 :=
    allCycleClauses_count_eq_two_of_mem_allOccurrenceVariables
      source copy copyOriginal
  rw [formulaOccurrences, List.count_append, sourceCount, cycleCount]

end PeriodicThreeSATThree
end LeanTrominoes
