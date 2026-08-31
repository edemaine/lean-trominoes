/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierModelTailData
import LeanTrominoes.RetainedAngularFanFinalCarrierOrderedTailDirections
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLinkInputLiteralTailDirections

/-! # Clockwise compiler-model tails of final carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalCarrierIndexedOccurrenceThreeOccurrenceDecidableEq

/-- The clockwise semantic tail table of one tagged final carrier clause is
its two exact compiler-model tails in the carrier formatter's order. -/
theorem FinalCarrierTaggedLinkInput.orderedTailDirections_eq_modelTails
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput source taggedLink clauseIndex)
    (nextSlice : Bool) :
    orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          (PeriodicThreeSATThree.formula source))
        clauseIndex
        (copiedOccurrenceClause
          (PeriodicThreeSATThree.formula source) clauseIndex
          ⟨(0, 0), normalizedCarrierClauseAt
            (PeriodicThreeSATThree.formula source) taggedLink⟩) =
      if taggedLink.2 then
        [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1,
          finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0]
      else if taggedLink.1.first.isHorizontal then
        [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1,
          finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0]
      else
        [finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0,
          finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1] := by
  let retained := PeriodicThreeSATThree.formula source
  have firstMember :
      (finalCarrierNormalizedLiteralAt retained taggedLink 0, 0) ∈
        (normalizedCarrierClauseAt retained taggedLink).zipIdx := by
    rw [normalizedCarrierClauseAt_zipIdx_eq_literal_pair]
    simp
  have secondMember :
      (finalCarrierNormalizedLiteralAt retained taggedLink 1, 1) ∈
        (normalizedCarrierClauseAt retained taggedLink).zipIdx := by
    rw [normalizedCarrierClauseAt_zipIdx_eq_literal_pair]
    simp
  have firstTailEq := input.literalPublicTailDirections
    (finalCarrierNormalizedLiteralAt retained taggedLink 0) 0
    firstMember nextSlice
  have secondTailEq := input.literalPublicTailDirections
    (finalCarrierNormalizedLiteralAt retained taggedLink 1) 1
    secondMember nextSlice
  exact input.orderedTailDirections_eq_of_tails
    (finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 0)
    (finalCarrierModelTailAt source taggedLink clauseIndex nextSlice 1)
    (by simpa [retained, finalCarrierModelTailAt,
      finalCarrierSemanticOccurrenceSlotAt] using firstTailEq)
    (by simpa [retained, finalCarrierModelTailAt,
      finalCarrierSemanticOccurrenceSlotAt] using secondTailEq)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
