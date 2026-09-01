/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendOrderedTailDirections

/-! # Decoded source-clause records of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- One tagged final bend clause decodes to its canonical bend profile and
the two exact normalized model tails in clockwise order. -/
theorem FinalBendTaggedBendInput.sourceClauseRecords_eq_modelTails
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    (input : FinalBendTaggedBendInput source taggedBend clauseIndex) :
    let retained := PeriodicThreeSATThree.formula source
    let geometry : BendFallbackRouteTailRecords.Geometry :=
      { firstPort := taggedBend.1.incomingPort
        secondPort := taggedBend.1.outgoingPort }
    let localClauseIndex : Nat := if taggedBend.2 then 0 else 1
    let firstTail :=
      (BendNormalizedFallbackRouteTailRecords.routeDirections geometry
        localClauseIndex 0
        (finalBendSemanticOccurrenceSlotAt retained taggedBend clauseIndex 0)).tail
    let secondTail :=
      (BendNormalizedFallbackRouteTailRecords.routeDirections geometry
        localClauseIndex 1
        (finalBendSemanticOccurrenceSlotAt retained taggedBend clauseIndex 1)).tail
    let profile := BinaryRouteTailRecordFormatter.descriptorProfile
      (bendClauseDescriptor geometry.firstPort geometry.secondPort
        false taggedBend.2)
    sourceClauseRecords
        (routedCopiedClauseProfile retained clauseIndex
          ⟨(0, 0), normalizedBendClauseAt retained taggedBend⟩)
        (orderedTailDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
            retained)
          clauseIndex
          (copiedOccurrenceClause retained clauseIndex
            ⟨(0, 0), normalizedBendClauseAt retained taggedBend⟩)) =
      sourceClauseRecords profile
        (if BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap profile then
          [secondTail, firstTail]
        else
          [firstTail, secondTail]) := by
  dsimp only
  rw [input.routedProfile_eq_bend]
  rw [input.orderedTailDirections_eq_modelTails]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
