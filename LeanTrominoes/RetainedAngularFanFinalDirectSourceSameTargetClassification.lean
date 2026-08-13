/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSharedTargetData
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions

/-!
# Classification of final direct routes at one target

The planar embedding forbids a crossover, routed-variable duplicator, and
routed-clause component from sharing a translated macrocell center.  Within
one permitted component family, distinct final source clauses select either
different local atlas incidences, different crossover clauses, or different
duplicator branches.  These are exactly the three finite same-target
separation certificates.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicOrthocrossing

set_option maxHeartbeats 8000000

private instance decidableForallFintype
    {α : Type*} [Fintype α]
    (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] :
    Decidable (∀ value, predicate value) :=
  Fintype.decidableForallFintype

/-- Every incidence route of one direct local clause has the same clause
endpoint. -/
theorem retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind :
    ∀ (kind : RetainedDirectClauseKind)
      (firstIndex secondIndex :
        Fin (retainedDirectSourcePrefixChoices kind).length),
      (retainedDirectSourceLocalRouteAt
          kind firstIndex).headD (0, 0) =
        (retainedDirectSourceLocalRouteAt
          kind secondIndex).headD (0, 0) := by
  native_decide

def RetainedDirectClauseKind.SameFamily
    (first second : RetainedDirectClauseKind) : Prop :=
  match first, second with
  | .crossover _, .crossover _ => True
  | .duplicator _ _, .duplicator _ _ => True
  | .routedClause, .routedClause => True
  | _, _ => False

private theorem point_eq_add_periodTranslation_sub_of_add_periodTranslations_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second firstShift secondShift : Cell)
    (equal :
      Cell.add first ((drawing graph).periodTranslation firstShift) =
        Cell.add second ((drawing graph).periodTranslation secondShift)) :
    first =
      Cell.add second
        ((drawing graph).periodTranslation
          (Cell.sub secondShift firstShift)) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases firstShift with ⟨firstShiftX, firstShiftY⟩
  rcases secondShift with ⟨secondShiftX, secondShiftY⟩
  simp only [PeriodicGridDrawing.periodTranslation,
    Cell.add, Cell.sub, Cell.scale, Prod.mk.injEq] at equal ⊢
  constructor
  · linear_combination equal.1
  · linear_combination equal.2

/-- Equal translated centers of successful final direct sources belong to
the same direct component family. -/
theorem retainedFinalDirectSourceCenterKinds_sameFamily
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    {firstKind secondKind : RetainedDirectClauseKind}
    {firstCenter secondCenter : Cell}
    (first :
      RetainedFinalDirectSourceCenterKind
        formula firstKind firstCenter)
    (second :
      RetainedFinalDirectSourceCenterKind
        formula secondKind secondCenter)
    (centersEqual : firstCenter = secondCenter) :
    firstKind.SameFamily secondKind := by
  cases first with
  | crossover
      firstClauseIndex firstCrossing firstShift firstCrossingMember =>
      cases second with
      | crossover =>
          trivial
      | duplicator
          secondArm secondClauseIndex secondSite secondShift
          secondSiteMember =>
          exfalso
          have pointEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub secondShift firstShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_add_periodTranslations_eq
                formula.incidenceGraph
                firstCrossing.point
                (liftedIncidenceVertexPosition formula
                  (.variable secondSite.1) secondSite.2)
                firstShift secondShift centersEqual
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstCrossingMember
              (drawingVariableRouteSite_vertex_mem
                formula secondSiteMember)
              (Cell.add secondSite.2
                (Cell.sub secondShift firstShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
      | routedClause secondSite secondShift secondSiteMember =>
          exfalso
          have pointEq :
              firstCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1)
                  (Cell.add secondSite.2
                    (Cell.sub secondShift firstShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_add_periodTranslations_eq
                formula.incidenceGraph
                firstCrossing.point
                (liftedIncidenceVertexPosition formula
                  (.clause secondSite.1) secondSite.2)
                firstShift secondShift centersEqual
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree firstCrossingMember
              (drawingClauseRouteSite_vertex_mem
                formula secondSiteMember)
              (Cell.add secondSite.2
                (Cell.sub secondShift firstShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
  | duplicator
      firstArm firstClauseIndex firstSite firstShift firstSiteMember =>
      cases second with
      | crossover
          secondClauseIndex secondCrossing secondShift
          secondCrossingMember =>
          exfalso
          have pointEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2
                    (Cell.sub firstShift secondShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_add_periodTranslations_eq
                formula.incidenceGraph
                secondCrossing.point
                (liftedIncidenceVertexPosition formula
                  (.variable firstSite.1) firstSite.2)
                secondShift firstShift centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondCrossingMember
              (drawingVariableRouteSite_vertex_mem
                formula firstSiteMember)
              (Cell.add firstSite.2
                (Cell.sub firstShift secondShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
      | duplicator =>
          trivial
      | routedClause secondSite secondShift secondSiteMember =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.variable firstSite.1)
                  (Cell.add firstSite.2 firstShift) =
                liftedIncidenceVertexPosition formula
                  (.clause secondSite.1)
                  (Cell.add secondSite.2 secondShift) := by
            rw [liftedIncidenceVertexPosition_periodTranslate,
              liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual
          have vertexData :=
            liftedDrawingVertexPosition_eq
              formula.incidenceGraph
              (drawingVariableRouteSite_vertex_mem
                formula firstSiteMember)
              (drawingClauseRouteSite_vertex_mem
                formula secondSiteMember)
              (by
                simpa [liftedIncidenceVertexPosition] using positionEq)
          cases vertexData.1
  | routedClause firstSite firstShift firstSiteMember =>
      cases second with
      | crossover
          secondClauseIndex secondCrossing secondShift
          secondCrossingMember =>
          exfalso
          have pointEq :
              secondCrossing.point =
                liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2
                    (Cell.sub firstShift secondShift)) := by
            rw [liftedIncidenceVertexPosition_periodTranslate]
            exact
              point_eq_add_periodTranslation_sub_of_add_periodTranslations_eq
                formula.incidenceGraph
                secondCrossing.point
                (liftedIncidenceVertexPosition formula
                  (.clause firstSite.1) firstSite.2)
                secondShift firstShift centersEqual.symm
          exact
            (orientedCrossing_point_ne_liftedVertexPosition
              wellFormed degree secondCrossingMember
              (drawingClauseRouteSite_vertex_mem
                formula firstSiteMember)
              (Cell.add firstSite.2
                (Cell.sub firstShift secondShift)))
              (by
                simpa [liftedIncidenceVertexPosition] using pointEq)
      | duplicator
          secondArm secondClauseIndex secondSite secondShift
          secondSiteMember =>
          exfalso
          have positionEq :
              liftedIncidenceVertexPosition formula
                  (.clause firstSite.1)
                  (Cell.add firstSite.2 firstShift) =
                liftedIncidenceVertexPosition formula
                  (.variable secondSite.1)
                  (Cell.add secondSite.2 secondShift) := by
            rw [liftedIncidenceVertexPosition_periodTranslate,
              liftedIncidenceVertexPosition_periodTranslate]
            exact centersEqual
          have vertexData :=
            liftedDrawingVertexPosition_eq
              formula.incidenceGraph
              (drawingClauseRouteSite_vertex_mem
                formula firstSiteMember)
              (drawingVariableRouteSite_vertex_mem
                formula secondSiteMember)
              (by
                simpa [liftedIncidenceVertexPosition] using positionEq)
          cases vertexData.1
      | routedClause =>
          trivial

theorem PositionedPeriodicCNF.canonicalClausePositions_ne_of_nodup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (positionsNodup :
      (source.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          placement)).Nodup)
    {firstClause secondClause : PositionedPeriodicClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈ source.clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈ source.clauses.zipIdx)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    PositionedPeriodicCNF.canonicalClausePosition
        placement firstClause ≠
      PositionedPeriodicCNF.canonicalClausePosition
        placement secondClause := by
  have firstLookup :
      source.clauses[firstClauseIndex]? = some firstClause :=
    (List.mem_zipIdx_iff_getElem?).mp firstClauseMember
  have secondLookup :
      source.clauses[secondClauseIndex]? = some secondClause :=
    (List.mem_zipIdx_iff_getElem?).mp secondClauseMember
  rcases List.getElem?_eq_some_iff.mp firstLookup with
    ⟨firstIndexLt, firstAt⟩
  rcases List.getElem?_eq_some_iff.mp secondLookup with
    ⟨secondIndexLt, secondAt⟩
  intro positionsEqual
  have firstMapIndexLt :
      firstClauseIndex <
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition
            placement)).length := by
    simpa using firstIndexLt
  have secondMapIndexLt :
      secondClauseIndex <
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition
            placement)).length := by
    simpa using secondIndexLt
  have mappedPositionsEqual :
      (source.clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition placement))[
          firstClauseIndex]'firstMapIndexLt =
        (source.clauses.map
          (PositionedPeriodicCNF.canonicalClausePosition placement))[
            secondClauseIndex]'secondMapIndexLt := by
    simp only [List.getElem_map]
    rw [firstAt, secondAt]
    exact positionsEqual
  apply clauseIndicesDifferent
  exact
    (positionsNodup.getElem_inj_iff
      (hi := firstMapIndexLt)
      (hj := secondMapIndexLt)).mp mappedPositionsEqual

/-- Different final source clause indices have different canonical clause
positions. -/
theorem retainedFinalCanonicalClausePositions_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) firstClause ≠
      PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) secondClause := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have retainedClausesNonempty :
      ∀ retainedClause ∈ retainedDrawingPlanarSATFormula formula,
        retainedClause.literals ≠ [] :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have positionsNodup :
      ((finalCoordinatedSource formula).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (finalCoordinatedPlacement formula))).Nodup := by
    change
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.map
        (PositionedPeriodicCNF.canonicalClausePosition
          (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
            formula))).Nodup
    exact
      deduplicated_canonicalClausePositions_nodup
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        retainedClausesNonempty
  exact
    PositionedPeriodicCNF.canonicalClausePositions_ne_of_nodup
      (finalCoordinatedSource formula)
      (finalCoordinatedPlacement formula)
      positionsNodup firstClauseMember secondClauseMember
      clauseIndicesDifferent

/-- The represented source endpoint of a successful direct choice is the
canonical position of its final source clause. -/
theorem retainedFinalDirectSourceRouteChoice_sourceSegment_start
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice) :
    choice.sourceSegment.start =
      PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause := by
  have representedHead :=
    retainedFinalDirectSourceRouteChoice_route_headD
      formula clauseIndex literalIndex choice choiceLookup
  have finalHead :=
    (finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember).1
  have finalHeadD :
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex).headD (0, 0) =
        PositionedPeriodicCNF.canonicalClausePosition
          (finalCoordinatedPlacement formula) clause := by
    have mapped :=
      congrArg (fun value : Option Cell => value.getD (0, 0))
        finalHead
    simpa using mapped
  rw [finalCoordinatedSourceRoutes, representedHead] at finalHeadD
  simpa [RetainedDirectSourceRouteChoice.sourceSegment]
    using finalHeadD

/-- The three finite atlas cases that can occur for two distinct direct
incidences occupying one physical component macrocell. -/
inductive RetainedDirectSourceSameTargetAtlasCase :
    RetainedDirectSourceRouteChoice →
      RetainedDirectSourceRouteChoice → Prop
  | crossover
      (origin : Cell)
      (firstClauseIndex secondClauseIndex : Fin 26)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.crossover secondClauseIndex)).length)
      (clausesDifferent :
        firstClauseIndex ≠ secondClauseIndex) :
      RetainedDirectSourceSameTargetAtlasCase
        ⟨origin, .crossover firstClauseIndex, firstIndex⟩
        ⟨origin, .crossover secondClauseIndex, secondIndex⟩
  | duplicator
      (origin : Cell)
      (firstArm secondArm : DuplicatorArm)
      (firstClauseIndex secondClauseIndex : Fin 2)
      (firstIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator firstArm firstClauseIndex)).length)
      (secondIndex :
        Fin
          (retainedDirectSourcePrefixChoices
            (.duplicator secondArm secondClauseIndex)).length)
      (branchesDifferent :
        (firstArm, firstClauseIndex) ≠
          (secondArm, secondClauseIndex)) :
      RetainedDirectSourceSameTargetAtlasCase
        ⟨origin, .duplicator firstArm firstClauseIndex, firstIndex⟩
        ⟨origin, .duplicator secondArm secondClauseIndex, secondIndex⟩

/-- Successful direct choices from different final source clauses at one
physical origin fall into one of the three finite same-target atlas cases. -/
theorem retainedFinalDirectSourceRouteChoices_sameTargetAtlasCase
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
    (originsEqual :
      firstChoice.origin = secondChoice.origin) :
    RetainedDirectSourceSameTargetAtlasCase
      firstChoice secondChoice := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula firstClauseIndex firstLiteralIndex
      firstChoice firstChoiceLookup with
    ⟨firstData⟩
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula secondClauseIndex secondLiteralIndex
      secondChoice secondChoiceLookup with
    ⟨secondData⟩
  have centersEqual : firstData.center = secondData.center := by
    apply Cell.scale_injective
      (show (planarMacroScale : Int) ≠ 0 by
        simp [planarMacroScale])
    rw [← firstData.originEq, ← secondData.originEq]
    exact originsEqual
  have sameFamily :=
    retainedFinalDirectSourceCenterKinds_sameFamily
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      firstData.centerKind secondData.centerKind centersEqual
  have canonicalStartsDifferent :=
    retainedFinalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      clauseIndicesDifferent
  have firstStart :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_start
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice
      firstClauseMember firstLiteralMember firstChoiceLookup
  have secondStart :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_start
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondChoice
      secondClauseMember secondLiteralMember secondChoiceLookup
  have sourceStartsDifferent :
      firstChoice.sourceSegment.start ≠
        secondChoice.sourceSegment.start := by
    rw [firstStart, secondStart]
    exact canonicalStartsDifferent
  rcases firstChoice with ⟨firstOrigin, firstKind, firstIndex⟩
  rcases secondChoice with ⟨secondOrigin, secondKind, secondIndex⟩
  simp only at originsEqual
  subst secondOrigin
  cases firstKind with
  | crossover firstClause =>
      cases secondKind with
      | crossover secondClause =>
          by_cases clausesEqual : firstClause = secondClause
          · subst secondClause
            exfalso
            apply sourceStartsDifferent
            simp only [RetainedDirectSourceRouteChoice.sourceSegment]
            rw [
              retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
                (.crossover firstClause) firstIndex secondIndex]
          · exact
              RetainedDirectSourceSameTargetAtlasCase.crossover
                firstOrigin firstClause secondClause
                firstIndex secondIndex clausesEqual
      | duplicator =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | routedClause =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
  | duplicator firstArm firstClause =>
      cases secondKind with
      | crossover =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | duplicator secondArm secondClause =>
          by_cases branchesEqual :
              (firstArm, firstClause) =
                (secondArm, secondClause)
          · cases branchesEqual
            exfalso
            apply sourceStartsDifferent
            simp only [RetainedDirectSourceRouteChoice.sourceSegment]
            rw [
              retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
                (.duplicator firstArm firstClause)
                firstIndex secondIndex]
          · exact
              RetainedDirectSourceSameTargetAtlasCase.duplicator
                firstOrigin firstArm secondArm
                firstClause secondClause
                firstIndex secondIndex branchesEqual
      | routedClause =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
  | routedClause =>
      cases secondKind with
      | crossover =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | duplicator =>
          simp [RetainedDirectClauseKind.SameFamily] at sameFamily
      | routedClause =>
          exfalso
          apply sourceStartsDifferent
          simp only [RetainedDirectSourceRouteChoice.sourceSegment]
          rw [
            retainedDirectSourceLocalRouteAt_headD_eq_of_sameKind
              .routedClause firstIndex secondIndex]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
