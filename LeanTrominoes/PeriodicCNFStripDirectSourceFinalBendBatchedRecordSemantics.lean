/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTaggedClauseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierEqualityData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance
import LeanTrominoes.RetainedAngularFanFinalBendRecordFamilySemantics

/-! # Batched semantics of direct final-bend clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendBatchedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendBatchedRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

private def expandedBendSourceClauseRecordAt
    (formulaEquality clauseEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (tagged : (RouteBend × Bool) × Nat) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  let positionedClause :
      PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨(0, 0), @normalizedBendClauseAt Variable clauseEquality
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

private def expandedBendSourceClauseRecords
    (formulaEquality clauseEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (routeBends : List RouteBend) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  ((routeBends.product [true, false]).zipIdx start).flatMap
    (expandedBendSourceClauseRecordAt
      formulaEquality clauseEquality formula)

private theorem expandedBendSourceClauseRecords_formulaEquality_irrel
    (first second clauseEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (start : Nat)
    (routeBends : List RouteBend) :
    expandedBendSourceClauseRecords first clauseEquality
        formula start routeBends =
      expandedBendSourceClauseRecords second clauseEquality
        formula start routeBends := by
  exact decidableEq_application_irrel
    (fun equality : DecidableEq Variable =>
      expandedBendSourceClauseRecords equality clauseEquality
        formula start routeBends)
    first second

private def positionedTaggedClauseSourceRecords
    (formulaEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (taggedClauses : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  (taggedClauses.map fun taggedClause =>
      (⟨(0, 0), taggedClause.1⟩, taggedClause.2)).flatMap
    fun taggedClause =>
      sourceClauseRecords
        (@routedCopiedClauseProfile Variable formulaEquality formula
          taggedClause.2 taggedClause.1)
        (orderedTailDirections
          (@retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            Variable formulaEquality formula)
          taggedClause.2
          (@copiedOccurrenceClause Variable formulaEquality formula
            taggedClause.2 taggedClause.1))

private def indexedNormalizedBendClauses
    (clauseEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (start : Nat) :
    List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (((baseRouteBends formula).product [true, false]).zipIdx start).map
    fun tagged =>
      (@normalizedBendClauseAt Variable clauseEquality formula tagged.1,
        tagged.2)

private theorem indexedNormalizedBendClauses_decidableEq_irrel
    (first second : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (start : Nat) :
    indexedNormalizedBendClauses first formula start =
      indexedNormalizedBendClauses second formula start := by
  exact decidableEq_application_irrel
    (fun equality : DecidableEq Variable =>
      indexedNormalizedBendClauses equality formula start)
    first second

private theorem genericExpandedBendRecords_eq_from
    (formula : PeriodicCNF Variable)
    (routeBends : List RouteBend)
    (start : Nat) :
    expandedBendSourceClauseRecords
        directSourceFinalOriginalVariableDecidableEq
        directSourceFinalOriginalVariableDecidableEq
        formula start routeBends =
      finalBendSourceClauseRecordsFrom formula start routeBends := by
  unfold expandedBendSourceClauseRecords
  change ((routeBends.product [true, false]).zipIdx start).flatMap
      (finalBendSourceClauseRecordsAt formula) =
    finalBendSourceClauseRecordsFrom formula start routeBends
  exact (finalBendSourceClauseRecordsFrom_eq_product
    formula routeBends start).symm

private def directSourceFinalBendExpandedSemanticRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  let formula := directSourceFinalNormalizedFormula decider symbols
  let routeBends := baseRouteBends formula
  let start := directSourceFinalBendStart decider symbols
  expandedBendSourceClauseRecords
    drawingOrderedThreeOccurrenceVariableInstDecidableEq
    directSourceFinalOriginalVariableDecidableEq
    formula start routeBends

private def directSourceFinalBendClauseExpandedSemanticRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  let formula := directSourceFinalNormalizedFormula decider symbols
  positionedTaggedClauseSourceRecords
    directSourceFinalOriginalVariableDecidableEq formula
    ((directSourceFinalBendClauses decider symbols).zipIdx
      (directSourceFinalBendStart decider symbols))

private theorem directSourceFinalBendBatchedSemanticRecords_eq_clauseExpanded
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) =
      directSourceFinalBendClauseExpandedSemanticRecords
        decider symbols := by
  rw [directSourceFormula_eq_finalNormalized]
  unfold directSourceFinalBendClauseExpandedSemanticRecords
  exact batchedRecords_retainedFinalNormalizedClauseSemantic
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalBendStart decider symbols)
    (directSourceFinalBendClauses decider symbols)

private def taggedBendClauseExpandedSemanticRecords
    (formulaEquality clauseEquality : DecidableEq Variable)
    (formula : PeriodicCNF Variable)
    (start : Nat) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  positionedTaggedClauseSourceRecords formulaEquality formula
    (indexedNormalizedBendClauses clauseEquality formula start)

private def directSourceFinalBendTaggedClauseExpandedSemanticRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  taggedBendClauseExpandedSemanticRecords
    directSourceFinalOriginalVariableDecidableEq
    directSourceFinalOriginalVariableDecidableEq
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalBendStart decider symbols)

private theorem directSourceFinalBendTaggedClauses_eq_original
    (symbols : List encoding.Γ) :
    (directSourceFinalBendClauses decider symbols).zipIdx
        (directSourceFinalBendStart decider symbols) =
      indexedNormalizedBendClauses
        directSourceFinalOriginalVariableDecidableEq
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols) := by
  unfold indexedNormalizedBendClauses
    directSourceFinalBendClauses directSourceFinalNormalizedFormula
    PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
  rw [baseBendNormalizedClauses_eq_map_baseTaggedBends,
    List.zipIdx_map]
  rfl

private theorem directSourceFinalBendClauseExpandedSemanticRecords_eq_tagged
    (symbols : List encoding.Γ) :
    directSourceFinalBendClauseExpandedSemanticRecords decider symbols =
      directSourceFinalBendTaggedClauseExpandedSemanticRecords
        decider symbols := by
  unfold directSourceFinalBendClauseExpandedSemanticRecords
    directSourceFinalBendTaggedClauseExpandedSemanticRecords
    taggedBendClauseExpandedSemanticRecords
  dsimp only
  exact congrArg
    (positionedTaggedClauseSourceRecords
      directSourceFinalOriginalVariableDecidableEq
      (directSourceFinalNormalizedFormula decider symbols))
    (directSourceFinalBendTaggedClauses_eq_original decider symbols)

private theorem taggedBendClauseExpandedSemanticRecords_eq_expanded
    (formula : PeriodicCNF Variable)
    (start : Nat) :
    taggedBendClauseExpandedSemanticRecords
        directSourceFinalOriginalVariableDecidableEq
        directSourceFinalOriginalVariableDecidableEq formula start =
      expandedBendSourceClauseRecords
        directSourceFinalOriginalVariableDecidableEq
        directSourceFinalOriginalVariableDecidableEq
        formula start (baseRouteBends formula) := by
  unfold taggedBendClauseExpandedSemanticRecords
    positionedTaggedClauseSourceRecords
    indexedNormalizedBendClauses expandedBendSourceClauseRecords
  rw [List.flatMap_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro tagged _taggedMember
  rfl

private theorem directSourceFinalBendTaggedClauseExpandedSemanticRecords_eq_expanded
    (symbols : List encoding.Γ) :
    directSourceFinalBendTaggedClauseExpandedSemanticRecords
        decider symbols =
      directSourceFinalBendExpandedSemanticRecords decider symbols := by
  unfold directSourceFinalBendTaggedClauseExpandedSemanticRecords
    directSourceFinalBendExpandedSemanticRecords
  dsimp only
  calc
    taggedBendClauseExpandedSemanticRecords
          directSourceFinalOriginalVariableDecidableEq
          directSourceFinalOriginalVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)
          (directSourceFinalBendStart decider symbols) =
        expandedBendSourceClauseRecords
          directSourceFinalOriginalVariableDecidableEq
          directSourceFinalOriginalVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (baseRouteBends
            (directSourceFinalNormalizedFormula decider symbols)) :=
      taggedBendClauseExpandedSemanticRecords_eq_expanded
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
    _ = expandedBendSourceClauseRecords
          drawingOrderedThreeOccurrenceVariableInstDecidableEq
          directSourceFinalOriginalVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (baseRouteBends
            (directSourceFinalNormalizedFormula decider symbols)) := by
      exact expandedBendSourceClauseRecords_formulaEquality_irrel
        directSourceFinalOriginalVariableDecidableEq
        drawingOrderedThreeOccurrenceVariableInstDecidableEq
        directSourceFinalOriginalVariableDecidableEq
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols))

private theorem directSourceFinalBendExpandedSemanticRecords_eq_source
    (symbols : List encoding.Γ) :
    directSourceFinalBendExpandedSemanticRecords decider symbols =
      finalBendSourceClauseRecordsFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)) := by
  unfold directSourceFinalBendExpandedSemanticRecords
  let formula := directSourceFinalNormalizedFormula decider symbols
  let routeBends := baseRouteBends formula
  let start := directSourceFinalBendStart decider symbols
  calc
    expandedBendSourceClauseRecords
          drawingOrderedThreeOccurrenceVariableInstDecidableEq
          directSourceFinalOriginalVariableDecidableEq
          formula start routeBends =
        expandedBendSourceClauseRecords
          directSourceFinalOriginalVariableDecidableEq
          directSourceFinalOriginalVariableDecidableEq
          formula start routeBends := by
      exact expandedBendSourceClauseRecords_formulaEquality_irrel
        drawingOrderedThreeOccurrenceVariableInstDecidableEq
        directSourceFinalOriginalVariableDecidableEq
        directSourceFinalOriginalVariableDecidableEq
        formula start routeBends
    _ = finalBendSourceClauseRecordsFrom formula start routeBends :=
      genericExpandedBendRecords_eq_from formula routeBends start

/-- Batching the direct bend-family semantic input produces exactly the
expanded semantic records in untranslated physical-bend order. -/
theorem directSourceFinalBendBatchedSemanticRecords_eq_sourceClauseRecords
    (symbols : List encoding.Γ) :
    HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) =
      finalBendSourceClauseRecordsFrom
        (directSourceFinalNormalizedFormula decider symbols)
        (directSourceFinalBendStart decider symbols)
        (baseRouteBends
          (directSourceFinalNormalizedFormula decider symbols)) := by
  exact (directSourceFinalBendBatchedSemanticRecords_eq_clauseExpanded
    decider symbols).trans
      ((directSourceFinalBendClauseExpandedSemanticRecords_eq_tagged
        decider symbols).trans
          ((directSourceFinalBendTaggedClauseExpandedSemanticRecords_eq_expanded
            decider symbols).trans
              (directSourceFinalBendExpandedSemanticRecords_eq_source
                decider symbols)))

end LeanTrominoes.PeriodicCNFStripReduction

end
