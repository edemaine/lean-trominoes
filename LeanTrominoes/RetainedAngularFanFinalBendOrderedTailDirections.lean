/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineBinaryTailClockwiseSemantics
import LeanTrominoes.RetainedAngularFanFinalBendLiteralTailDirections
import LeanTrominoes.RetainedAngularFanFinalBendRoutedProfileSemantics

/-! # Clockwise semantic tails of final retained-bend clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open UnaryProgramClauseProfile

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

/-- A tagged final bend clause has the two normalized compiler tails in the
clockwise order selected by its descriptor profile. -/
theorem FinalBendTaggedBendInput.orderedTailDirections_eq_modelTails
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
    orderedTailDirections
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          retained)
        clauseIndex
        (copiedOccurrenceClause retained clauseIndex
          ⟨(0, 0), normalizedBendClauseAt retained taggedBend⟩) =
      if BinaryRouteTailRecordClockwiseRelabel.profileNeedsSwap profile then
        [secondTail, firstTail]
      else
        [firstTail, secondTail] := by
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let positionedClause : PositionedPeriodicClause
      (WrappedPeriodicPlanarSATVariable
        (ThreeOccurrenceVariable Variable)) :=
    ⟨(0, 0), normalizedBendClauseAt retained taggedBend⟩
  let copiedClause := copiedOccurrenceClause retained clauseIndex
    positionedClause
  let routes :=
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
      retained
  let geometry : BendFallbackRouteTailRecords.Geometry :=
    { firstPort := taggedBend.1.incomingPort
      secondPort := taggedBend.1.outgoingPort }
  have lengthEq : copiedClause.literals.length = 2 := by
    simp [copiedClause, positionedClause, copiedOccurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceClause,
      normalizedBendClauseAt_eq_literal_pair]
  have firstMember :
      (finalBendNormalizedLiteralAt retained taggedBend 0, 0) ∈
        (normalizedBendClauseAt retained taggedBend).zipIdx := by
    rw [normalizedBendClauseAt_zipIdx_eq_literal_pair]
    simp
  have secondMember :
      (finalBendNormalizedLiteralAt retained taggedBend 1, 1) ∈
        (normalizedBendClauseAt retained taggedBend).zipIdx := by
    rw [normalizedBendClauseAt_zipIdx_eq_literal_pair]
    simp
  let firstInput : FinalBendTaggedLiteralInput source taggedBend clauseIndex
      (finalBendNormalizedLiteralAt retained taggedBend 0) 0 :=
    { bendInput := input
      literalMember := firstMember }
  let secondInput : FinalBendTaggedLiteralInput source taggedBend clauseIndex
      (finalBendNormalizedLiteralAt retained taggedBend 1) 1 :=
    { bendInput := input
      literalMember := secondMember }
  have firstTailEq := firstInput.publicTailDirections
  have secondTailEq := secondInput.publicTailDirections
  rcases taggedBend with ⟨routeBend, forward⟩
  cases forward with
  | false =>
      have profileEq := input.routedProfile_eq_bend
      have binaryProfile :
          DirectedClauseProfile.ofClause routes clauseIndex copiedClause =
            .binary ⟨false, false⟩
              (bendRouteFirstDirection routeBend.incomingPort
                routeBend.outgoingPort 1 0)
              ⟨false, true⟩
              (bendRouteFirstDirection routeBend.incomingPort
                routeBend.outgoingPort 1 1) := by
        simpa [retained, positionedClause, copiedClause, routes,
          routedCopiedClauseProfile,
          BinaryRouteTailRecordFormatter.descriptorProfile,
          bendClauseDescriptor] using profileEq
      have ordered := orderedTailDirections_eq_of_binary_profile_swap
        routes clauseIndex copiedClause
        (⟨false, false⟩ : LiteralProfile) ⟨false, true⟩
        (bendRouteFirstDirection routeBend.incomingPort
          routeBend.outgoingPort 1 0)
        (bendRouteFirstDirection routeBend.incomingPort
          routeBend.outgoingPort 1 1)
        (BendNormalizedFallbackRouteTailRecords.routeDirections geometry 1 0
          (finalBendSemanticOccurrenceSlotAt retained (routeBend, false)
            clauseIndex 0)).tail
        (BendNormalizedFallbackRouteTailRecords.routeDirections geometry 1 1
          (finalBendSemanticOccurrenceSlotAt retained (routeBend, false)
            clauseIndex 1)).tail
        binaryProfile lengthEq
        (by simpa [retained, geometry, finalBendSemanticOccurrenceSlotAt]
          using firstTailEq)
        (by simpa [retained, geometry, finalBendSemanticOccurrenceSlotAt]
          using secondTailEq)
      simpa [retained, positionedClause, copiedClause, routes, geometry,
        BinaryRouteTailRecordFormatter.descriptorProfile,
        bendClauseDescriptor] using ordered
  | true =>
      have profileEq := input.routedProfile_eq_bend
      have binaryProfile :
          DirectedClauseProfile.ofClause routes clauseIndex copiedClause =
            .binary ⟨false, true⟩
              (bendRouteFirstDirection routeBend.incomingPort
                routeBend.outgoingPort 0 0)
              ⟨false, false⟩
              (bendRouteFirstDirection routeBend.incomingPort
                routeBend.outgoingPort 0 1) := by
        simpa [retained, positionedClause, copiedClause, routes,
          routedCopiedClauseProfile,
          BinaryRouteTailRecordFormatter.descriptorProfile,
          bendClauseDescriptor] using profileEq
      have ordered := orderedTailDirections_eq_of_binary_profile_swap
        routes clauseIndex copiedClause
        (⟨false, true⟩ : LiteralProfile) ⟨false, false⟩
        (bendRouteFirstDirection routeBend.incomingPort
          routeBend.outgoingPort 0 0)
        (bendRouteFirstDirection routeBend.incomingPort
          routeBend.outgoingPort 0 1)
        (BendNormalizedFallbackRouteTailRecords.routeDirections geometry 0 0
          (finalBendSemanticOccurrenceSlotAt retained (routeBend, true)
            clauseIndex 0)).tail
        (BendNormalizedFallbackRouteTailRecords.routeDirections geometry 0 1
          (finalBendSemanticOccurrenceSlotAt retained (routeBend, true)
            clauseIndex 1)).tail
        binaryProfile lengthEq
        (by simpa [retained, geometry, finalBendSemanticOccurrenceSlotAt]
          using firstTailEq)
        (by simpa [retained, geometry, finalBendSemanticOccurrenceSlotAt]
          using secondTailEq)
      simpa [retained, positionedClause, copiedClause, routes, geometry,
        BinaryRouteTailRecordFormatter.descriptorProfile,
        bendClauseDescriptor] using ordered

end PeriodicEightOccurrenceSplit
end LeanTrominoes
