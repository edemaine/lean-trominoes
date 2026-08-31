/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierDecodedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTaggedClauseSemantics
import LeanTrominoes.RetainedAngularFanNormalizedClauseBatchedRecordSemantics

/-! # Batched semantics of direct final-carrier clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierBatchedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalStructuralBaseDecidableEq
attribute [local instance]
  directSourceFinalStructuralBaseDecidableEq

private def expandedCarrierSourceClauseRecordAt
    (formulaEquality clauseEquality : DecidableEq Variable)
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (tagged : (EqualityLink CarrierNode × Bool) × Nat) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  let formula := @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
    directSourceFinalStructuralBaseDecidableEq source
  let positionedClause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨(0, 0), @normalizedCarrierClauseAt Variable clauseEquality
      formula tagged.1⟩
  sourceClauseRecords
    (@routedCopiedClauseProfile Variable formulaEquality formula
      tagged.2 positionedClause)
    (orderedTailDirections
      (@retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        Variable formulaEquality formula)
      tagged.2
      (@copiedOccurrenceClause Variable formulaEquality formula
        tagged.2 positionedClause))

private theorem genericExpandedCarrierRecords_eq_from
    (source : PeriodicCNF (ThreeCNFVariable Nat))
    (links : List (EqualityLink CarrierNode))
    (start : Nat) :
    ((links.product [true, false]).zipIdx start).flatMap
        (expandedCarrierSourceClauseRecordAt
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq source) =
      finalCarrierSourceClauseRecordsFrom source start links := by
  change ((links.product [true, false]).zipIdx start).flatMap
      (finalCarrierSourceClauseRecordsAt source) =
    finalCarrierSourceClauseRecordsFrom source start links
  exact (finalCarrierSourceClauseRecordsFrom_eq_product
    source links start).symm

/-- Batching the direct carrier-family semantic input produces exactly the
generic expanded semantic records in physical-link order. -/
theorem directSourceFinalCarrierBatchedSemanticRecords_eq_sourceClauseRecords
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) =
      finalCarrierSourceClauseRecordsFrom
        (directThreeCNFSourceFormula decider symbols)
        (finalCarrierStart
          (directThreeCNFSourceFormula decider symbols))
        (finalCarrierPhysicalLinks
          (directThreeCNFSourceFormula decider symbols)) := by
  have formulaEq :
      directSourceFinalNormalizedFormula decider symbols =
        @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat)
          directSourceFinalStructuralBaseDecidableEq
          (directThreeCNFSourceFormula decider symbols) := by
    unfold directSourceFinalNormalizedFormula
    exact decidableEq_application_irrel
      (fun equality : DecidableEq (ThreeCNFVariable Nat) =>
        @PeriodicThreeSATThree.formula (ThreeCNFVariable Nat) equality
          (directThreeCNFSourceFormula decider symbols))
      directSourceFinalOriginalBaseDecidableEq
      directSourceFinalStructuralBaseDecidableEq
  rw [directSourceFormula_eq_finalNormalized]
  rw [batchedRecords_retainedFinalNormalizedClauseSemantic]
  rw [directSourceFinalCarrierTaggedClauses_eq]
  rw [List.flatMap_map]
  rw [directSourceFinalCarrierTaggedLinks_eq_generic]
  unfold finalCarrierTaggedLinks finalCarrierTaggedLinksFrom
  rw [finalCarrierTaggedLinkValues_eq_physicalProduct]
  rw [List.flatMap_map]
  rw [formulaEq]
  generalize directThreeCNFSourceFormula decider symbols = source
  generalize finalCarrierPhysicalLinks source = links
  generalize finalCarrierStart source = start
  change ((links.product [true, false]).zipIdx start).flatMap
      (expandedCarrierSourceClauseRecordAt
        drawingOrderedThreeOccurrenceVariableInstDecidableEq
        directFinalCarrierTaggedClauseVariableDecidableEq source) =
    finalCarrierSourceClauseRecordsFrom source start links
  calc
    ((links.product [true, false]).zipIdx start).flatMap
        (expandedCarrierSourceClauseRecordAt
          drawingOrderedThreeOccurrenceVariableInstDecidableEq
          directFinalCarrierTaggedClauseVariableDecidableEq source) =
      ((links.product [true, false]).zipIdx start).flatMap
        (expandedCarrierSourceClauseRecordAt
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
          directFinalCarrierTaggedClauseVariableDecidableEq source) := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          ((links.product [true, false]).zipIdx start).flatMap
            (expandedCarrierSourceClauseRecordAt equality
              directFinalCarrierTaggedClauseVariableDecidableEq source))
        drawingOrderedThreeOccurrenceVariableInstDecidableEq
        finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
    _ = ((links.product [true, false]).zipIdx start).flatMap
        (expandedCarrierSourceClauseRecordAt
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
          finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
          source) := by
      exact decidableEq_application_irrel
        (fun equality : DecidableEq Variable =>
          ((links.product [true, false]).zipIdx start).flatMap
            (expandedCarrierSourceClauseRecordAt
              finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
              equality source))
        directFinalCarrierTaggedClauseVariableDecidableEq
        finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq
    _ = finalCarrierSourceClauseRecordsFrom source start links :=
      genericExpandedCarrierRecords_eq_from source links start

/-- Thus the batched direct carrier semantics is exactly the clockwise
decoding of the declarative normalized compiler blocks. -/
theorem directSourceFinalCarrierBatchedSemanticRecords_eq_decodedRecords
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) =
      BinaryRouteTailRecordClockwiseRelabel.decodedRecords
        (directSourceFinalCarrierNormalizedFallbackRecordBlocks
          decider symbols) := by
  rw [directSourceFinalCarrierBatchedSemanticRecords_eq_sourceClauseRecords]
  exact directSourceFinalCarrierSourceClauseRecords_eq_decodedRecords
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
