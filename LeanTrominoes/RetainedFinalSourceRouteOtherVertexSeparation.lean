/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreePositionedSourceVariables
import LeanTrominoes.PositionedPeriodicCNFSourceVertexDistinctness
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.RetainedFinalRoutePrefixSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRoutePointOccurrences

/-!
# Clearing a final source-route prefix from another source vertex

An implication-cycle block is centered at the base position of an occurring
source atom.  To expose that point to retained periodic planarity, choose any
source incidence witnessing the atom and translate its route by the negative
of its relative literal offset.  The translated route then ends exactly at
the atom's base position.  Endpoint-only route contact and simplicity clear
every other copied-source prefix from that point.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- If a genuine final source incidence ends at a different periodic
occurrence from an atom's base position, then its deleted-final-point prefix
contains neither that base point nor an axis-aligned segment through it. -/
theorem finalCoordinatedSourceRoutePrefix_avoids_sourceVariablePosition
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          targetAtom) :
    (∀ point ∈
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).dropLast,
        point ≠
          (finalCoordinatedPlacement formula).position
            targetAtom) ∧
      ∀ segment ∈
        gridPolylineSegments
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains
            ((finalCoordinatedPlacement formula).position
              targetAtom) := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  let currentRoute := routes clauseIndex literalIndex
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, targetClauseIndex,
      targetLiteral, targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  let targetRoute :=
    routes targetClauseIndex targetLiteralIndex
  let targetShift :=
    Cell.neg
      (incidenceRelativeOffset
        targetClause targetLiteral)
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        clauseMember literalMember with
    ⟨currentRouteIndex, currentIncidenceMember,
      currentRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        targetClauseMember targetLiteralMember with
    ⟨targetRouteIndex, targetIncidenceMember,
      targetRouteMember⟩
  have currentRouteMember' :
      (currentRoute, currentRouteIndex) ∈
        drawing.edgeRoutes.zipIdx := by
    simp only [source, placement, routes,
      finalCoordinatedSource,
      finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes]
      at currentRouteMember
    change
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex literalIndex,
        currentRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx
      at currentRouteMember
    simpa [currentRoute, routes, drawing,
      finalCoordinatedSourceRoutes] using
      currentRouteMember
  have targetRouteMember' :
      (targetRoute, targetRouteIndex) ∈
        drawing.edgeRoutes.zipIdx := by
    simp only [source, placement, routes,
      finalCoordinatedSource,
      finalCoordinatedPlacement,
      finalCoordinatedSourceRoutes]
      at targetRouteMember
    change
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula targetClauseIndex targetLiteralIndex,
        targetRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx
      at targetRouteMember
    simpa [targetRoute, routes, drawing,
      finalCoordinatedSourceRoutes] using
      targetRouteMember
  have currentLength : 2 ≤ currentRoute.length := by
    simpa [currentRoute, routes] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have targetLength : 2 ≤ targetRoute.length := by
    simpa [targetRoute, routes] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        targetClauseMember targetLiteralMember
  have currentEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have targetEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      targetClauseMember targetLiteralMember
  have relativeZero_of_targetShiftZero
      (targetShiftZero : targetShift = (0, 0)) :
      incidenceRelativeOffset
          targetClause targetLiteral =
        (0, 0) := by
    rcases relativeEq :
        incidenceRelativeOffset
          targetClause targetLiteral with
      ⟨relativeX, relativeY⟩
    simp only [targetShift, relativeEq, Cell.neg,
      Cell.sub, Prod.mk.injEq] at targetShiftZero
    exact Prod.ext (by omega) (by omega)
  have targetCanonicalAtBase
      (targetShiftZero : targetShift = (0, 0)) :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement targetClause targetLiteral =
        placement.position targetAtom := by
    have relativeZero :=
      relativeZero_of_targetShiftZero targetShiftZero
    change
      Cell.add
          (placement.position targetLiteral.atom)
          (placement.translation
            (incidenceRelativeOffset
              targetClause targetLiteral)) =
        placement.position targetAtom
    rw [relativeZero, targetAtomEqual]
    simp [PeriodicVariablePlacement.translation,
      Cell.add, Cell.scale]
  have occurrencesDifferent :
      (currentRouteIndex, ((0, 0) : Cell)) ≠
        (targetRouteIndex, targetShift) := by
    intro occurrencesEqual
    have routeIndicesEqual :
        currentRouteIndex = targetRouteIndex :=
      congrArg Prod.fst occurrencesEqual
    have targetShiftZero :
        targetShift = (0, 0) :=
      (congrArg Prod.snd occurrencesEqual).symm
    have incidencesEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        currentIncidenceMember targetIncidenceMember
        routeIndicesEqual
    have canonicalPositionsEqual :
        PositionedPeriodicCNF.canonicalLiteralPosition
            placement clause literal =
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement targetClause targetLiteral := by
      have equal :=
        congrArg
          (fun tagged :
              CNFIncidence
                  (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
            Cell.add
              (placement.position tagged.1.literal.atom)
              (placement.translation
                (Cell.sub tagged.1.literal.offset
                  (PeriodicCNF.clauseAnchor
                    tagged.1.clause))))
          incidencesEqual
      simpa [PositionedPeriodicCNF.canonicalLiteralPosition]
        using equal
    apply centersDifferent
    simpa [placement] using
      canonicalPositionsEqual.trans
        (targetCanonicalAtBase targetShiftZero)
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have translatedAvoid :=
    PeriodicGridDrawing.routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isContinuouslyPlanar
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsAvoidInteriors
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_routePointsMeetOnlyAtEndpoints
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty)
      currentRouteMember' targetRouteMember'
      currentLength targetLength
      (0, 0) targetShift occurrencesDifferent
  have currentTranslationZero :
      drawing.periodTranslation (0, 0) = (0, 0) := by
    simp [drawing,
      PeriodicGridDrawing.periodTranslation,
      Cell.scale]
  have currentMapZero :
      currentRoute.map (Cell.add (0, 0)) =
        currentRoute := by
    induction currentRoute with
    | nil => rfl
    | cons point points induction =>
        rw [List.map_cons, induction]
        simp [Cell.add]
  have rawAvoid :
      RoutesAvoidEachOther
        currentRoute
        (targetRoute.map
          (Cell.add
            (drawing.periodTranslation targetShift))) := by
    rw [currentTranslationZero, currentMapZero]
      at translatedAvoid
    exact translatedAvoid
  have currentNodup : currentRoute.Nodup := by
    simpa [currentRoute, routes,
      finalCoordinatedSourceRoutes] using
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        (clause, clauseIndex)
        (by simpa [source, finalCoordinatedSource]
          using clauseMember)
        (literal, literalIndex) literalMember).1
  have translatedTargetLast :
      (targetRoute.map
        (Cell.add
          (drawing.periodTranslation targetShift))).getLast? =
        some (placement.position targetAtom) := by
    rw [List.getLast?_map]
    have targetLast :
        targetRoute.getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement targetClause targetLiteral) := by
      simpa [targetRoute, routes, placement] using
        targetEndpoints.2
    rw [targetLast]
    apply congrArg some
    rw [
      retainedDeduplicatedGaugedWrappedDrawing_periodTranslation_eq_placement]
    change
      Cell.add
          (placement.translation targetShift)
          (Cell.add
            (placement.position targetLiteral.atom)
            (placement.translation
              (incidenceRelativeOffset
                targetClause targetLiteral))) =
        placement.position targetAtom
    rcases targetPositionEq :
        placement.position targetAtom with
      ⟨targetX, targetY⟩
    rcases relativeEq :
        incidenceRelativeOffset
          targetClause targetLiteral with
      ⟨relativeX, relativeY⟩
    simp only [targetShift, relativeEq,
      PeriodicVariablePlacement.translation,
      Cell.neg, Cell.sub, Cell.scale, Cell.add,
      targetAtomEqual, targetPositionEq, Prod.mk.injEq]
    constructor <;> ring
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have sourceNeTarget :
      PositionedPeriodicCNF.canonicalClausePosition
          placement clause ≠
        placement.position targetAtom := by
    have distinct :=
      @PositionedPeriodicCNF.canonicalClausePosition_ne_variablePosition_of_members
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        source placement routes compatible
        clause targetClause clauseIndex targetClauseIndex
        clauseMember literal literalIndex literalMember
        targetClauseMember targetLiteral targetLiteralIndex
        targetLiteralMember
    simpa [targetAtomEqual] using distinct
  have prefixAvoid :=
    routePrefix_avoids_other_final_point_of_avoid
      rawAvoid currentNodup
      (by
        simpa [currentRoute, routes, placement] using
          currentEndpoints.1)
      translatedTargetLast sourceNeTarget
  simpa [currentRoute, routes, placement] using
    prefixAvoid

end PeriodicOrthocrossing
end LeanTrominoes
