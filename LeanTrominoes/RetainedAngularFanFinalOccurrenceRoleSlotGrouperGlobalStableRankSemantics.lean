/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalOccurrenceRoleSlotGrouperQueryBlockSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankSlotBlocks

/-! # Grouping global stable-rank slots by indexed clause queries -/

noncomputable section

namespace LeanTrominoes.FinalOccurrenceRoleSlotGrouper

open PeriodicEightOccurrenceSplit

/-- For any nonempty width-three source and matching indexed query column,
grouping the global bounded stable-rank stream produces exactly one query and
packed slot block per source clause. -/
theorem slotInputsOfQueries_globalStableRanks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (query : PeriodicClause Variable × Nat → Query)
    (clausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (clausesWidth : ∀ clause ∈ source.clauses, clause.length ≤ 3)
    (queryArityEq : ∀ taggedClause ∈ source.clauses.zipIdx,
      queryArity (query taggedClause) = taggedClause.1.length) :
    slotInputsOfQueries
        (source.clauses.zipIdx.map query)
        (BoundedRetainedTerminalSlots.slots
          (retainedOccurrenceGlobalStableTerminalRanks source routes)) =
      source.clauses.zipIdx.map fun taggedClause =>
        (query taggedClause,
          RetainedDirectClauseOccurrenceSlots.ofList
            (retainedOccurrenceGlobalStableTerminalSlotBlock
              source routes taggedClause)) := by
  rw [← retainedOccurrenceGlobalStableTerminalSlotBlocks_flatten]
  unfold retainedOccurrenceGlobalStableTerminalSlotBlocks
  change slotInputsOfQueries
      (source.clauses.zipIdx.map query)
      (source.clauses.zipIdx.flatMap
        (retainedOccurrenceGlobalStableTerminalSlotBlock source routes)) = _
  apply slotInputsOfQueries_map_flatMap
  · intro taggedClause taggedClauseMember
    have clauseNonempty := clausesNonempty taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
    intro blockNil
    have lengthZero := congrArg List.length blockNil
    unfold retainedOccurrenceGlobalStableTerminalSlotBlock at lengthZero
    simp only [List.length_map, List.length_zipIdx, List.length_nil]
      at lengthZero
    exact clauseNonempty (List.length_eq_zero_iff.mp lengthZero)
  · intro taggedClause taggedClauseMember
    unfold retainedOccurrenceGlobalStableTerminalSlotBlock
    simp only [List.length_map, List.length_zipIdx]
    exact clausesWidth taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)
  · intro taggedClause taggedClauseMember
    unfold retainedOccurrenceGlobalStableTerminalSlotBlock
    simp only [List.length_map, List.length_zipIdx]
    exact queryArityEq taggedClause taggedClauseMember

end LeanTrominoes.FinalOccurrenceRoleSlotGrouper

end
