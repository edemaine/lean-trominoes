/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankStream
import LeanTrominoes.UnaryFieldBoundedRetainedTerminalSlotCompiler

/-! # Clause blocks of global stable-rank terminal slots -/

namespace LeanTrominoes.PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- One clause's presentation-ordered bounded global stable-rank slots. -/
def retainedOccurrenceGlobalStableTerminalSlotBlock
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (taggedClause : PeriodicClause Variable × Nat) :
    List RetainedTerminalSlot :=
  taggedClause.1.zipIdx.map fun taggedLiteral =>
    boundedRetainedTerminalSlot
      (retainedOccurrenceGlobalStableTerminalRank source routes
        (taggedLiteral.1.atom, taggedClause.2, taggedLiteral.2))

@[simp] theorem retainedOccurrenceGlobalStableTerminalSlotBlock_length
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (taggedClause : PeriodicClause Variable × Nat) :
    (retainedOccurrenceGlobalStableTerminalSlotBlock
      source routes taggedClause).length = taggedClause.1.length := by
  unfold retainedOccurrenceGlobalStableTerminalSlotBlock
  simp only [List.length_map, List.length_zipIdx]

/-- Presentation-ordered bounded stable-rank slots, grouped by source
clause while retaining the global clause and literal indices. -/
def retainedOccurrenceGlobalStableTerminalSlotBlocks
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    List (List RetainedTerminalSlot) :=
  source.clauses.zipIdx.map
    (retainedOccurrenceGlobalStableTerminalSlotBlock source routes)

theorem retainedOccurrenceGlobalStableTerminalSlotBlocks_lengths
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTerminalSlotBlocks source routes).map
        List.length =
      source.clauses.map List.length := by
  have zipLengths : ∀ (clauses : List (PeriodicClause Variable))
      (start : Nat),
      (clauses.zipIdx start).map (fun taggedClause =>
          taggedClause.1.length) =
        clauses.map List.length := by
    intro clauses start
    induction clauses generalizing start with
    | nil => rfl
    | cons clause clauses induction =>
        simp only [List.zipIdx_cons, List.map_cons, List.cons.injEq,
          true_and]
        exact induction (start + 1)
  unfold retainedOccurrenceGlobalStableTerminalSlotBlocks
  rw [List.map_map]
  calc
    _ = source.clauses.zipIdx.map (fun taggedClause =>
          taggedClause.1.length) := by
      apply List.map_congr_left
      intro taggedClause _taggedMember
      exact retainedOccurrenceGlobalStableTerminalSlotBlock_length
        source routes taggedClause
    _ = source.clauses.map List.length := zipLengths source.clauses 0

/-- Flattening the clause blocks recovers exactly the existing global
bounded stable-rank slot stream. -/
theorem retainedOccurrenceGlobalStableTerminalSlotBlocks_flatten
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (retainedOccurrenceGlobalStableTerminalSlotBlocks
        source routes).flatten =
      BoundedRetainedTerminalSlots.slots
        (retainedOccurrenceGlobalStableTerminalRanks source routes) := by
  rw [retainedOccurrenceGlobalStableTerminalRanks_eq_map]
  unfold retainedOccurrenceGlobalStableTerminalSlotBlocks
    retainedOccurrenceGlobalStableTerminalSlotBlock
    BoundedRetainedTerminalSlots.slots allOccurrenceVariables
    taggedLiterals
  simp [List.map_map, List.map_flatMap, Function.comp_def]
  unfold List.flatMap
  rfl

end LeanTrominoes.PeriodicEightOccurrenceSplit
