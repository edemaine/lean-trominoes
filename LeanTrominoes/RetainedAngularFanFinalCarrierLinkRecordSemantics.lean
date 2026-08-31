/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedFallbackClockwiseRecordSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierModelTailLinkGeometry
import LeanTrominoes.RetainedAngularFanFinalCarrierSourceClauseRecordSemantics

/-! # Decoded record semantics of one final retained carrier link -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The forward and backward semantic clauses of one physical carrier link
decode to the compiler's corresponding normalized four-route block. -/
theorem finalCarrierSourceClauseRecords_pair_eq_decodedBlock
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {link : EqualityLink CarrierNode}
    {forwardClauseIndex backwardClauseIndex : Nat}
    (forwardInput : FinalCarrierTaggedLinkInput source (link, true)
      forwardClauseIndex)
    (backwardInput : FinalCarrierTaggedLinkInput source (link, false)
      backwardClauseIndex) :
    sourceClauseRecords
          (routedCopiedClauseProfile
            (PeriodicThreeSATThree.formula source) forwardClauseIndex
            ⟨(0, 0), normalizedCarrierClauseAt
              (PeriodicThreeSATThree.formula source) (link, true)⟩)
          (orderedTailDirections
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              (PeriodicThreeSATThree.formula source))
            forwardClauseIndex
            (copiedOccurrenceClause
              (PeriodicThreeSATThree.formula source) forwardClauseIndex
              ⟨(0, 0), normalizedCarrierClauseAt
                (PeriodicThreeSATThree.formula source) (link, true)⟩)) ++
        sourceClauseRecords
          (routedCopiedClauseProfile
            (PeriodicThreeSATThree.formula source) backwardClauseIndex
            ⟨(0, 0), normalizedCarrierClauseAt
              (PeriodicThreeSATThree.formula source) (link, false)⟩)
          (orderedTailDirections
            (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
              (PeriodicThreeSATThree.formula source))
            backwardClauseIndex
            (copiedOccurrenceClause
              (PeriodicThreeSATThree.formula source) backwardClauseIndex
              ⟨(0, 0), normalizedCarrierClauseAt
                (PeriodicThreeSATThree.formula source) (link, false)⟩)) =
      BinaryRouteTailRecordClockwiseRelabel.decodedBlockRecords
        (CarrierNormalizedFallbackRouteTailRecords.block
          (CarrierFallbackRouteTailRecords.Geometry.ofLink
            (PeriodicThreeSATThree.formula source) link)
          (finalCarrierSemanticOccurrenceSlotAt source (link, true)
            forwardClauseIndex 0)
          (finalCarrierSemanticOccurrenceSlotAt source (link, true)
            forwardClauseIndex 1)
          (finalCarrierSemanticOccurrenceSlotAt source (link, false)
            backwardClauseIndex 0)
          (finalCarrierSemanticOccurrenceSlotAt source (link, false)
            backwardClauseIndex 1)) := by
  have decEq :
      (finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq :
        DecidableEq (ThreeOccurrenceVariable Variable)) =
        drawingOrderedThreeOccurrenceVariableInstDecidableEq :=
    Subsingleton.elim _ _
  have forwardFirstTail :=
    finalCarrierModelDirectionWord_tail_eq_ofLink source link true 0
      (finalCarrierSemanticOccurrenceSlotAt source (link, true)
        forwardClauseIndex 0)
  have forwardSecondTail :=
    finalCarrierModelDirectionWord_tail_eq_ofLink source link true 1
      (finalCarrierSemanticOccurrenceSlotAt source (link, true)
        forwardClauseIndex 1)
  have backwardFirstTail :=
    finalCarrierModelDirectionWord_tail_eq_ofLink source link false 0
      (finalCarrierSemanticOccurrenceSlotAt source (link, false)
        backwardClauseIndex 0)
  have backwardSecondTail :=
    finalCarrierModelDirectionWord_tail_eq_ofLink source link false 1
      (finalCarrierSemanticOccurrenceSlotAt source (link, false)
        backwardClauseIndex 1)
  rw [← decEq] at forwardFirstTail forwardSecondTail backwardFirstTail backwardSecondTail
  rw [forwardInput.sourceClauseRecords_eq_modelTails
      (carrierLinkNextSlice (PeriodicThreeSATThree.formula source) link),
    backwardInput.sourceClauseRecords_eq_modelTails
      (carrierLinkNextSlice (PeriodicThreeSATThree.formula source) link),
    CarrierNormalizedFallbackRouteTailRecords.decodedBlockRecords_block]
  simp only [eq_self, Bool.false_eq_true, if_true, if_false]
  unfold finalCarrierModelTailAt
  rw [forwardFirstTail, forwardSecondTail,
    backwardFirstTail, backwardSecondTail]
  simp only [eq_self, Bool.false_eq_true, if_true, if_false,
    CarrierFallbackRouteTailRecords.Geometry.ofLink,
    Fin.val_zero, Fin.val_one]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
