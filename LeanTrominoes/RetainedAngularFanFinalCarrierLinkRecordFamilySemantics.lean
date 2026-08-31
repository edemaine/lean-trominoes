/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLinkRecordSemantics

/-! # Decoded record semantics of final retained carrier-link families -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNFStripReduction
open PeriodicOrthocrossing
open PlanarThreeSAT

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- Expanded semantic records of one globally indexed tagged carrier link. -/
def finalCarrierSourceClauseRecordsAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : (EqualityLink CarrierNode × Bool) × Nat) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  sourceClauseRecords
    (routedCopiedClauseProfile
      (PeriodicThreeSATThree.formula source) tagged.2
      ⟨(0, 0), normalizedCarrierClauseAt
        (PeriodicThreeSATThree.formula source) tagged.1⟩)
    (orderedTailDirections
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        (PeriodicThreeSATThree.formula source))
      tagged.2
      (copiedOccurrenceClause
        (PeriodicThreeSATThree.formula source) tagged.2
        ⟨(0, 0), normalizedCarrierClauseAt
          (PeriodicThreeSATThree.formula source) tagged.1⟩))

/-- The normalized four-route block selected by the two directed global
clause indices of one physical carrier link. -/
def finalCarrierNormalizedRecordBlockAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (forwardClauseIndex backwardClauseIndex : Nat) :
    BinaryRouteTailRecordBatchFormatter.Block :=
  CarrierNormalizedFallbackRouteTailRecords.block
    (CarrierFallbackRouteTailRecords.Geometry.ofLink
      (PeriodicThreeSATThree.formula source) link)
    (finalCarrierSemanticOccurrenceSlotAt source (link, true)
      forwardClauseIndex 0)
    (finalCarrierSemanticOccurrenceSlotAt source (link, true)
      forwardClauseIndex 1)
    (finalCarrierSemanticOccurrenceSlotAt source (link, false)
      backwardClauseIndex 0)
    (finalCarrierSemanticOccurrenceSlotAt source (link, false)
      backwardClauseIndex 1)

/-- Expanded semantic carrier records, grouped recursively by physical link. -/
def finalCarrierSourceClauseRecordsFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Nat → List (EqualityLink CarrierNode) →
      List HorizontalRoutedRouteHeaderTail.Token
  | _, [] => []
  | start, link :: links =>
      finalCarrierSourceClauseRecordsAt source ((link, true), start) ++
        finalCarrierSourceClauseRecordsAt source
            ((link, false), start + 1) ++
          finalCarrierSourceClauseRecordsFrom source (start + 2) links

/-- Normalized compiler blocks in the same physical-link grouping. -/
def finalCarrierNormalizedRecordBlocksFrom
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    Nat → List (EqualityLink CarrierNode) →
      List BinaryRouteTailRecordBatchFormatter.Block
  | _, [] => []
  | start, link :: links =>
      finalCarrierNormalizedRecordBlockAt source link start (start + 1) ::
        finalCarrierNormalizedRecordBlocksFrom source (start + 2) links

/-- Per-link correctness lifts to every indexed carrier-link family. -/
theorem finalCarrierSourceClauseRecordsFrom_eq_decodedRecords
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (sourceInput : FinalCarrierSourceInput source)
    (links : List (EqualityLink CarrierNode))
    (start : Nat)
    (indexed : ∀ tagged ∈ (links.product [true, false]).zipIdx start,
      finalCarrierTaggedLinkIndexed source tagged.1 tagged.2) :
    finalCarrierSourceClauseRecordsFrom source start links =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (finalCarrierNormalizedRecordBlocksFrom source start links) := by
  induction links generalizing start with
  | nil => rfl
  | cons link links induction =>
      have forwardMember :
          ((link, true), start) ∈
            ((link :: links).product [true, false]).zipIdx start := by
        simp [List.product]
      have backwardMember :
          ((link, false), start + 1) ∈
            ((link :: links).product [true, false]).zipIdx start := by
        simp [List.product]
      let forwardInput : FinalCarrierTaggedLinkInput source (link, true) start :=
        { sourceInput := sourceInput
          taggedLinkIndexed := indexed _ forwardMember }
      let backwardInput : FinalCarrierTaggedLinkInput source (link, false)
          (start + 1) :=
        { sourceInput := sourceInput
          taggedLinkIndexed := indexed _ backwardMember }
      have tailIndexed :
          ∀ tagged ∈ (links.product [true, false]).zipIdx (start + 2),
            finalCarrierTaggedLinkIndexed source tagged.1 tagged.2 := by
        intro tagged taggedMember
        apply indexed tagged
        simpa [List.product, Nat.add_assoc] using
          (Or.inr (Or.inr taggedMember))
      rw [finalCarrierSourceClauseRecordsFrom,
        finalCarrierNormalizedRecordBlocksFrom,
        BinaryRouteTailRecordClockwiseRelabel.decodedRecords,
        List.flatMap_cons]
      rw [show
        finalCarrierSourceClauseRecordsAt source ((link, true), start) ++
            finalCarrierSourceClauseRecordsAt source
              ((link, false), start + 1) =
          BinaryRouteTailRecordClockwiseRelabel.decodedBlockRecords
            (finalCarrierNormalizedRecordBlockAt source link start
              (start + 1)) by
        exact finalCarrierSourceClauseRecords_pair_eq_decodedBlock
          forwardInput backwardInput]
      rw [induction (start + 2) tailIndexed]
      rfl

end PeriodicEightOccurrenceSplit
end LeanTrominoes
