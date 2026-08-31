/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockData
import LeanTrominoes.RetainedAngularFanFinalBendNormalizedLiteralData
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutes

/-! # Presentation forms of final retained-bend record families -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Semantic occurrence slot of one globally indexed normalized bend
literal. -/
def finalBendSemanticOccurrenceSlotAt
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (literalIndex : Fin 2) : RetainedTerminalSlot :=
  retainedFinalCoordinatedOccurrenceSlot formula
    (finalBendNormalizedLiteralAt formula taggedBend literalIndex)
    clauseIndex literalIndex

/-- Clause-based semantic slot blocks with independently named equality
implementations for clause normalization and route-slot evaluation. -/
def finalBendSemanticOccurrenceSlotBlocksAt
    {Variable : Type}
    (clauseEquality slotEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (taggedBends : List ((RouteBend × Bool) × Nat)) :
    List (List RetainedTerminalSlot) :=
  (taggedBends.map fun tagged =>
    (@normalizedBendClauseAt Variable clauseEquality
      formula tagged.1, tagged.2)).map fun taggedClause =>
        taggedClause.1.zipIdx.map fun taggedLiteral =>
          @retainedFinalCoordinatedOccurrenceSlot Variable slotEquality
            formula taggedLiteral.1 taggedClause.2 taggedLiteral.2

/-- Named two-slot semantic blocks over the same indexed tagged-bend
presentation. -/
def finalBendNamedSemanticOccurrenceSlotBlocksAt
    {Variable : Type}
    (equality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (taggedBends : List ((RouteBend × Bool) × Nat)) :
    List (List RetainedTerminalSlot) :=
  taggedBends.map fun tagged =>
    [@finalBendSemanticOccurrenceSlotAt Variable equality
        formula tagged.1 tagged.2 0,
      @finalBendSemanticOccurrenceSlotAt Variable equality
        formula tagged.1 tagged.2 1]

/-- With a common equality implementation, clause-based slot blocks reduce
pointwise to their two named semantic slots. -/
theorem finalBendSemanticOccurrenceSlotBlocksAt_eq_named
    {Variable : Type}
    (equality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (taggedBends : List ((RouteBend × Bool) × Nat)) :
    finalBendSemanticOccurrenceSlotBlocksAt
        equality equality formula taggedBends =
      finalBendNamedSemanticOccurrenceSlotBlocksAt
        equality formula taggedBends := by
  induction taggedBends with
  | nil => rfl
  | cons tagged taggedBends induction =>
      simp only [finalBendSemanticOccurrenceSlotBlocksAt,
        finalBendNamedSemanticOccurrenceSlotBlocksAt, List.map_cons]
      rw [@normalizedBendClauseAt_zipIdx_eq_literal_pair Variable
        equality formula tagged.1]
      simp only [List.map_cons, List.map_nil]
      change _ :: finalBendSemanticOccurrenceSlotBlocksAt
          equality equality formula taggedBends =
        _ :: finalBendNamedSemanticOccurrenceSlotBlocksAt
          equality formula taggedBends
      rw [induction]
      simp only [finalBendSemanticOccurrenceSlotAt,
        Fin.val_zero, Fin.val_one]

/-- The four semantic occurrence slots of each physical bend, recursively
aligned with its forward and backward global clause indices. -/
def finalBendSemanticOccurrenceSlotsFrom
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Nat → List RouteBend → List RetainedTerminalSlot
  | _, [] => []
  | start, routeBend :: routeBends =>
      [finalBendSemanticOccurrenceSlotAt formula (routeBend, true)
          start 0,
        finalBendSemanticOccurrenceSlotAt formula (routeBend, true)
          start 1,
        finalBendSemanticOccurrenceSlotAt formula (routeBend, false)
          (start + 1) 0,
        finalBendSemanticOccurrenceSlotAt formula (routeBend, false)
          (start + 1) 1] ++
        finalBendSemanticOccurrenceSlotsFrom formula (start + 2) routeBends

/-- The normalized four-route record block selected by the two directed
global clause indices of one physical bend. -/
def finalBendNormalizedRecordBlockAt
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (forwardClauseIndex backwardClauseIndex : Nat) :
    BinaryRouteTailRecordBatchFormatter.Block :=
  BendNormalizedFallbackRouteTailRecords.block
    { firstPort := routeBend.incomingPort
      secondPort := routeBend.outgoingPort }
    (finalBendSemanticOccurrenceSlotAt formula (routeBend, true)
      forwardClauseIndex 0)
    (finalBendSemanticOccurrenceSlotAt formula (routeBend, true)
      forwardClauseIndex 1)
    (finalBendSemanticOccurrenceSlotAt formula (routeBend, false)
      backwardClauseIndex 0)
    (finalBendSemanticOccurrenceSlotAt formula (routeBend, false)
      backwardClauseIndex 1)

/-- Normalized bend compiler blocks in physical-bend grouping. -/
def finalBendNormalizedRecordBlocksFrom
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    Nat → List RouteBend →
      List BinaryRouteTailRecordBatchFormatter.Block
  | _, [] => []
  | start, routeBend :: routeBends =>
      finalBendNormalizedRecordBlockAt formula routeBend start (start + 1) ::
        finalBendNormalizedRecordBlocksFrom formula (start + 2) routeBends

/-- Recursive four-slot grouping is the ordinary clause-major flattening of
the tagged-bend product presentation. -/
theorem finalBendSemanticOccurrenceSlotsFrom_eq_product
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBends : List RouteBend)
    (start : Nat) :
    finalBendSemanticOccurrenceSlotsFrom formula start routeBends =
      ((routeBends.product [true, false]).zipIdx start).flatMap fun tagged =>
        [finalBendSemanticOccurrenceSlotAt formula tagged.1 tagged.2 0,
          finalBendSemanticOccurrenceSlotAt formula tagged.1 tagged.2 1] := by
  induction routeBends generalizing start with
  | nil => rfl
  | cons routeBend routeBends induction =>
      simp only [finalBendSemanticOccurrenceSlotsFrom]
      rw [induction (start + 2)]
      rfl

/-- Recursive block grouping is exactly the normalized bend block zipper on
the aligned geometry and semantic-slot streams. -/
theorem finalBendNormalizedRecordBlocksFrom_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBends : List RouteBend)
    (start : Nat) :
    finalBendNormalizedRecordBlocksFrom formula start routeBends =
      BendNormalizedFallbackRouteTailRecords.blocks
        (routeBends.map fun routeBend =>
          ({ firstPort := routeBend.incomingPort
             secondPort := routeBend.outgoingPort } :
            BendFallbackRouteTailRecords.Geometry))
        (finalBendSemanticOccurrenceSlotsFrom formula start routeBends) := by
  induction routeBends generalizing start with
  | nil => rfl
  | cons routeBend routeBends induction =>
      simp only [finalBendNormalizedRecordBlocksFrom,
        finalBendSemanticOccurrenceSlotsFrom, List.map_cons]
      rw [induction (start + 2)]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
