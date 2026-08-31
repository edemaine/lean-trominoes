/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailData
import LeanTrominoes.RetainedAngularFanFinalCarrierOrderedModelTailDirections
import LeanTrominoes.RetainedAngularFanFinalCarrierRoutedProfileSemantics

/-! # Decoded source-clause records of final retained carriers -/

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

/-- One tagged final carrier clause decodes to its canonical carrier profile
and the two exact model tails in clockwise order. -/
theorem FinalCarrierTaggedLinkInput.sourceClauseRecords_eq_modelTails
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput source taggedLink clauseIndex)
    (nextSlice : Bool) :
    sourceClauseRecords
        (routedCopiedClauseProfile
          (PeriodicThreeSATThree.formula source) clauseIndex
          ⟨(0, 0), normalizedCarrierClauseAt
            (PeriodicThreeSATThree.formula source) taggedLink⟩)
        (orderedTailDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            (PeriodicThreeSATThree.formula source))
          clauseIndex
          (copiedOccurrenceClause
            (PeriodicThreeSATThree.formula source) clauseIndex
            ⟨(0, 0), normalizedCarrierClauseAt
              (PeriodicThreeSATThree.formula source) taggedLink⟩)) =
      sourceClauseRecords
        (BinaryRouteTailRecordFormatter.descriptorProfile
          (carrierClauseDescriptor taggedLink.1.first.isHorizontal
            (carrierLinkNextSlice
              (PeriodicThreeSATThree.formula source) taggedLink.1)
            taggedLink.2))
        (if taggedLink.2 then
          [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1,
            finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0]
        else if taggedLink.1.first.isHorizontal then
          [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1,
            finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0]
        else
          [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0,
            finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1]) := by
  rw [input.routedProfile_eq_carrier,
    input.orderedTailDirections_eq_modelTails]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
