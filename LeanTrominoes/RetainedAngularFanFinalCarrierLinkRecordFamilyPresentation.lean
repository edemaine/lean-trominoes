/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordFamilySemantics

/-! # Presentation forms of final retained carrier-link record families -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing
open PlanarThreeSAT

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The four semantic occurrence slots of each physical link, recursively
aligned with the two directed global clause indices. -/
def finalCarrierSemanticOccurrenceSlotsFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Nat → List (EqualityLink CarrierNode) → List RetainedTerminalSlot
  | _, [] => []
  | start, link :: links =>
      [finalCarrierSemanticOccurrenceSlotAt source (link, true) start 0,
        finalCarrierSemanticOccurrenceSlotAt source (link, true) start 1,
        finalCarrierSemanticOccurrenceSlotAt source (link, false)
          (start + 1) 0,
        finalCarrierSemanticOccurrenceSlotAt source (link, false)
          (start + 1) 1] ++
        finalCarrierSemanticOccurrenceSlotsFrom source (start + 2) links

/-- Recursive grouping is the ordinary clause-major flattening of the
Boolean-product presentation. -/
theorem finalCarrierSourceClauseRecordsFrom_eq_product
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    finalCarrierSourceClauseRecordsFrom source start links =
      ((links.product [true, false]).zipIdx start).flatMap
        (finalCarrierSourceClauseRecordsAt source) := by
  induction links generalizing start with
  | nil => rfl
  | cons link links induction =>
      simp only [finalCarrierSourceClauseRecordsFrom, List.append_assoc]
      rw [induction (start + 2)]
      congr 1

/-- The recursive four-slot stream is the same clause-major flattening of
the indexed tagged-link presentation. -/
theorem finalCarrierSemanticOccurrenceSlotsFrom_eq_product
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    finalCarrierSemanticOccurrenceSlotsFrom source start links =
      ((links.product [true, false]).zipIdx start).flatMap fun tagged =>
        [finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 0,
          finalCarrierSemanticOccurrenceSlotAt source tagged.1 tagged.2 1] := by
  induction links generalizing start with
  | nil => rfl
  | cons link links induction =>
      simp only [finalCarrierSemanticOccurrenceSlotsFrom]
      rw [induction (start + 2)]
      rfl

/-- The recursive block normal form is exactly the normalized carrier block
zipper on the aligned geometry and semantic-slot streams. -/
theorem finalCarrierNormalizedRecordBlocksFrom_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    finalCarrierNormalizedRecordBlocksFrom source start links =
      CarrierNormalizedFallbackRouteTailRecords.blocks
        (links.map (CarrierFallbackRouteTailRecords.Geometry.ofLink
          (PeriodicThreeSATThree.formula source)))
        (finalCarrierSemanticOccurrenceSlotsFrom source start links) := by
  induction links generalizing start with
  | nil => rfl
  | cons link links induction =>
      simp only [finalCarrierNormalizedRecordBlocksFrom,
        finalCarrierSemanticOccurrenceSlotsFrom, List.map_cons]
      rw [induction (start + 2)]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
