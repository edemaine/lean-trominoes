/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactVariableCount

/-! # Endpoint membership of occurrence-cycle links -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

theorem cycleLink_fst_mem
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable))
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (linkMember : link ∈ cycleLinks copies) :
    link.1 ∈ copies := by
  have clauseMember : implicationClause link.1 link.2 ∈
      cycleClauses copies := by
    rw [cycleClauses_eq_map_cycleLinks]
    exact List.mem_map.mpr ⟨link, linkMember, rfl⟩
  apply cycleClauses_variableOccurrences_subset copies
  unfold PeriodicCNF.variableOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨implicationClause link.1 link.2, clauseMember, ?_⟩
  simp [implicationClause]

theorem cycleLink_snd_mem
    {Variable : Type*}
    (copies : List (ThreeOccurrenceVariable Variable))
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (linkMember : link ∈ cycleLinks copies) :
    link.2 ∈ copies := by
  have clauseMember : implicationClause link.1 link.2 ∈
      cycleClauses copies := by
    rw [cycleClauses_eq_map_cycleLinks]
    exact List.mem_map.mpr ⟨link, linkMember, rfl⟩
  apply cycleClauses_variableOccurrences_subset copies
  unfold PeriodicCNF.variableOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨implicationClause link.1 link.2, clauseMember, ?_⟩
  simp [implicationClause]

/-- Every first endpoint in the grouped link stream is a genuine source
occurrence copy. -/
theorem allCycleLink_fst_mem_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (linkMember : link ∈ allCycleLinks source) :
    link.1 ∈ allOccurrenceVariables source := by
  rw [show allCycleLinks source =
      (sourceVariables source).flatMap fun atom =>
        cycleLinks (occurrenceVariables source atom) by rfl,
    List.mem_flatMap] at linkMember
  obtain ⟨atom, atomMember, linkMember⟩ := linkMember
  have endpointMember := cycleLink_fst_mem
    (occurrenceVariables source atom) link linkMember
  rw [occurrenceVariables_eq_filter] at endpointMember
  exact List.mem_of_mem_filter endpointMember

/-- Every second endpoint in the grouped link stream is a genuine source
occurrence copy. -/
theorem allCycleLink_snd_mem_allOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : ThreeOccurrenceVariable Variable ×
      ThreeOccurrenceVariable Variable)
    (linkMember : link ∈ allCycleLinks source) :
    link.2 ∈ allOccurrenceVariables source := by
  rw [show allCycleLinks source =
      (sourceVariables source).flatMap fun atom =>
        cycleLinks (occurrenceVariables source atom) by rfl,
    List.mem_flatMap] at linkMember
  obtain ⟨atom, atomMember, linkMember⟩ := linkMember
  have endpointMember := cycleLink_snd_mem
    (occurrenceVariables source atom) link linkMember
  rw [occurrenceVariables_eq_filter] at endpointMember
  exact List.mem_of_mem_filter endpointMember

end PeriodicThreeSATThree
end LeanTrominoes
