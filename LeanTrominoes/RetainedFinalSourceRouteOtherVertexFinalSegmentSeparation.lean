/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalFallbackOwnCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexSeparation

/-!
# Clearing a fallback final segment from another source vertex

The translated-incidence argument clears the deleted-final-point prefix from
another source vertex.  For a fallback route, failed direct selection also
certifies orthogonality.  Retained periodic vertex planarity excludes the
other source vertex from the relative interior of the discarded final
segment, while prefix and final-endpoint inequalities exclude its endpoints.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Failure of the direct selector certifies orthogonality already before
the source-clearance scaling. -/
theorem finalCoordinatedFallbackSourceRoute_orthogonal
    {Variable : Type*} [DecidableEq Variable]
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
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    OrthogonalPolyline
      (finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex) := by
  let route :=
    finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex
  have scaledOrthogonal :
      OrthogonalPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          route) := by
    simpa [route] using
      finalCoordinatedScaledFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember choiceNone
  rw [orthogonalPolyline_iff_segments] at scaledOrthogonal ⊢
  intro segment segmentMember
  have scaledMember :
      segment.scale
          retainedAngularFanSourceClearanceFactor ∈
        gridPolylineSegments
          (scalePolyline
            retainedAngularFanSourceClearanceFactor
            route) := by
    rw [gridPolylineSegments_scalePolyline]
    exact List.mem_map.mpr
      ⟨segment, segmentMember, rfl⟩
  exact
    (GridSegment.isAxisAligned_scale_iff
      (by
        exact_mod_cast
          retainedAngularFanSourceClearanceFactor_pos)
      segment).mp
        (scaledOrthogonal _ scaledMember)

/-- The segment discarded by `dropLast` is a genuine segment of every final
coordinated source route. -/
theorem finalCoordinatedSourceRoute_finalSegment_mem
    {Variable : Type*} [DecidableEq Variable]
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    finalSegment ∈ gridPolylineSegments route := by
  dsimp only
  let routes := finalCoordinatedSourceRoutes formula
  let route := routes clauseIndex literalIndex
  let finalPoint := route.getLastD (0, 0)
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route, finalPoint⟩
  change finalSegment ∈ gridPolylineSegments route
  have routeLength : 2 ≤ route.length := by
    simpa [route, routes] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have routeFinal :
      route.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal) := by
    simpa [route, routes] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  have reverseTailExists :
      ∃ entrance, route.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      route routeLength
  have entranceLast :
      route.dropLast.getLast? =
        some (polylineLastEntrance route) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have dropLastNonempty : route.dropLast ≠ [] := by
    intro empty
    rw [empty] at entranceLast
    simp at entranceLast
  have routeDecomposition :
      route.dropLast ++ [finalPoint] = route := by
    apply List.dropLast_append_getLast?
    simp [finalPoint, List.getLastD_eq_getLast?,
      routeFinal]
  have entranceLastD :
      route.dropLast.getLastD (0, 0) =
        polylineLastEntrance route := by
    simp [List.getLastD_eq_getLast?, entranceLast]
  rw [← routeDecomposition,
    gridPolylineSegments_append_singleton_of_ne_nil
      route.dropLast (0, 0) finalPoint
      dropLastNonempty,
    List.mem_append]
  apply Or.inr
  simp only [List.mem_singleton]
  simpa [finalSegment] using entranceLastD.symm

/-- A fallback route's discarded final segment is axis-aligned. -/
theorem finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
    {Variable : Type*} [DecidableEq Variable]
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
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none) :
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    finalSegment.IsAxisAligned := by
  dsimp only
  let route :=
    finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route,
      route.getLastD (0, 0)⟩
  have routeOrthogonal :
      OrthogonalPolyline route := by
    simpa [route] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember choiceNone
  have finalSegmentMember :
      finalSegment ∈ gridPolylineSegments route := by
    simpa [route, finalSegment] using
      finalCoordinatedSourceRoute_finalSegment_mem
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
  rw [orthogonalPolyline_iff_segments] at routeOrthogonal
  exact routeOrthogonal _ finalSegmentMember

/-- A genuine positioned literal contributes its variable position to the
stored incidence-vertex position list. -/
theorem
    positionedLiteralPosition_mem_incidenceVertexPositions_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    placement.position literal.atom ∈
      PositionedPeriodicCNF.incidenceVertexPositions
        source placement := by
  have erasedClauseMember :
      clause.literals ∈ source.erase.clauses := by
    change
      clause.literals ∈
        source.clauses.map
          PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨clause,
        List.fst_mem_of_mem_zipIdx clauseMember,
        rfl⟩
  have occurrenceMember :
      literal.atom ∈ source.erase.variableOccurrences :=
    List.mem_flatMap.mpr
      ⟨clause.literals, erasedClauseMember,
        List.mem_map.mpr
          ⟨literal,
            List.fst_mem_of_mem_zipIdx literalMember,
            rfl⟩⟩
  have variablePrefixMember :
      CNFVertex.variable literal.atom ∈
        source.erase.incidenceVariableVertices := by
    exact List.mem_map.mpr
      ⟨literal.atom,
        List.mem_dedup.mpr occurrenceMember, rfl⟩
  unfold PositionedPeriodicCNF.incidenceVertexPositions
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨CNFVertex.variable literal.atom,
    variablePrefixMember, rfl⟩

/-- A genuine positioned literal contributes its atom to the erased raw
variable-occurrence list, independently of any deduplication instance. -/
theorem positionedLiteral_atom_mem_variableOccurrences_of_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    literal.atom ∈ source.erase.variableOccurrences := by
  have erasedClauseMember :
      clause.literals ∈ source.erase.clauses := by
    change
      clause.literals ∈
        source.clauses.map
          PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨clause,
        List.fst_mem_of_mem_zipIdx clauseMember,
        rfl⟩
  exact
    List.mem_flatMap.mpr
      ⟨clause.literals, erasedClauseMember,
        List.mem_map.mpr
          ⟨literal,
            List.fst_mem_of_mem_zipIdx literalMember,
            rfl⟩⟩

/-- A genuine positioned literal contributes its variable vertex to the
erased incidence graph. -/
theorem positionedLiteral_variableVertex_mem_incidenceGraph_of_members
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    CNFVertex.variable literal.atom ∈
      source.erase.incidenceGraph.vertices := by
  have erasedClauseMember :
      clause.literals ∈ source.erase.clauses := by
    change
      clause.literals ∈
        source.clauses.map
          PositionedPeriodicClause.literals
    exact List.mem_map.mpr
      ⟨clause,
        List.fst_mem_of_mem_zipIdx clauseMember,
        rfl⟩
  have occurrenceMember :
      literal.atom ∈ source.erase.variableOccurrences :=
    List.mem_flatMap.mpr
      ⟨clause.literals, erasedClauseMember,
        List.mem_map.mpr
          ⟨literal,
            List.fst_mem_of_mem_zipIdx literalMember,
            rfl⟩⟩
  change
    CNFVertex.variable literal.atom ∈
      PeriodicCNF.incidenceVariableVertices source.erase ++
        PeriodicCNF.incidenceClauseVertices source.erase
  apply List.mem_append_left
  exact List.mem_map.mpr
    ⟨literal.atom,
      List.mem_dedup.mpr occurrenceMember, rfl⟩

/-- Every occurring final source variable lies in the generic positioned
incidence-vertex position list. -/
theorem
    finalCoordinatedSourceVariablePosition_mem_incidenceVertexPositions
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase) :
    (finalCoordinatedPlacement formula).position targetAtom ∈
      PositionedPeriodicCNF.incidenceVertexPositions
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula) := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, _targetClauseIndex,
      targetLiteral, _targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  have targetLiteralPositionMember :=
    positionedLiteralPosition_mem_incidenceVertexPositions_of_members
      source placement
      targetClauseMember targetLiteralMember
  rw [targetAtomEqual] at targetLiteralPositionMember
  change
    placement.position targetAtom ∈
      PositionedPeriodicCNF.incidenceVertexPositions
        source placement
  exact targetLiteralPositionMember

/-- Every occurring final source variable is a genuine vertex of the
erased final incidence graph. -/
theorem finalCoordinatedSourceVariable_vertex_mem_incidenceGraph
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase) :
    CNFVertex.variable targetAtom ∈
      (finalCoordinatedSource formula).erase.incidenceGraph.vertices := by
  let source := finalCoordinatedSource formula
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, _targetClauseIndex,
      targetLiteral, _targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  have targetLiteralVertexMember :=
    positionedLiteral_variableVertex_mem_incidenceGraph_of_members
      source targetClauseMember targetLiteralMember
  rw [targetAtomEqual] at targetLiteralVertexMember
  exact targetLiteralVertexMember

set_option maxHeartbeats 8000000 in
/-- Every occurring source variable's final placement is stored directly
in the named retained drawing's standard-instance vertex list. -/
theorem finalCoordinatedSourceVariablePosition_mem_namedVertexPositions
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase) :
    (finalCoordinatedPlacement formula).position targetAtom ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).vertexPositions := by
  let source := finalCoordinatedSource formula
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, _targetClauseIndex,
      targetLiteral, _targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  have targetOccurrence :
      targetAtom ∈ source.erase.variableOccurrences := by
    have literalOccurrence :=
      positionedLiteral_atom_mem_variableOccurrences_of_members
        source targetClauseMember targetLiteralMember
    rw [targetAtomEqual] at literalOccurrence
    exact literalOccurrence
  unfold finalCoordinatedPlacement
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
    PositionedPeriodicCNF.incidenceDrawing
    PositionedPeriodicCNF.incidenceVertexPositions
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨CNFVertex.variable targetAtom, ?_, rfl⟩
  unfold PeriodicCNF.incidenceVariableVertices
  apply List.mem_map.mpr
  exact
    ⟨targetAtom,
      (@List.mem_dedup
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        targetAtom source.erase.variableOccurrences).mpr
          targetOccurrence,
      rfl⟩

/-- Vertex planarity applies directly to every segment of a stored route
when both periodic translates are zero. -/
theorem verticesAvoidRouteInteriors_of_route_segment_mem
    (drawing : PeriodicGridDrawing)
    (verticesAvoid : drawing.VerticesAvoidRouteInteriors)
    {vertexPosition : Cell}
    (vertexMember :
      vertexPosition ∈ drawing.vertexPositions)
    {route : List Cell}
    {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments route) :
    ¬segment.InteriorContains vertexPosition := by
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEqual⟩
  let indexedSegment : IndexedGridSegment :=
    ⟨routeIndex, segmentIndex,
      (gridPolylineSegments route).get segmentIndex⟩
  have indexedSegmentMember :
      indexedSegment ∈ drawing.indexedSegments :=
    PeriodicGridDrawing.indexedSegment_mem_of_route_mem
      routeMember segmentIndex
  have avoids :=
    verticesAvoid
      vertexPosition vertexMember
      indexedSegment indexedSegmentMember
      (0, 0) (0, 0)
  have zeroTranslation :
      drawing.periodTranslation (0, 0) = (0, 0) := by
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.scale]
  rw [zeroTranslation] at avoids
  have untranslatedAvoids :
      ¬indexedSegment.segment.InteriorContains
        vertexPosition := by
    simpa [GridSegment.translate, Cell.add] using avoids
  have indexedSegmentEqual :
      indexedSegment.segment = segment := by
    exact segmentEqual
  rw [indexedSegmentEqual] at untranslatedAvoids
  exact untranslatedAvoids

/-- Every genuine final coordinated source route occurs in the named
retained drawing. -/
theorem finalCoordinatedSourceRoute_mem_namedDrawing
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ routeIndex,
      (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex,
        routeIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx := by
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula)
        (finalCoordinatedSourceRoutes formula)
        clauseMember literalMember with
    ⟨routeIndex, _incidenceMember,
      routeMember⟩
  simp only [finalCoordinatedSource,
    finalCoordinatedPlacement, finalCoordinatedSourceRoutes]
    at routeMember
  change
    (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula clauseIndex literalIndex,
      routeIndex) ∈
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).edgeRoutes.zipIdx
    at routeMember
  exact ⟨routeIndex, by
    simpa only [finalCoordinatedSourceRoutes] using
      routeMember⟩

/-- Retained vertex planarity keeps every occurring source-variable
position out of the relative interior of a final source-route segment. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_avoidsInterior_sourceVariablePosition_of_certificate
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (certificate : RetainedPlanarSATCertificate formula)
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
          (finalCoordinatedSource formula).erase) :
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    ¬finalSegment.InteriorContains
      ((finalCoordinatedPlacement formula).position
        targetAtom) := by
  dsimp only
  let placement := finalCoordinatedPlacement formula
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  let route :=
    finalCoordinatedSourceRoutes
      formula clauseIndex literalIndex
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route,
      route.getLastD (0, 0)⟩
  have finalSegmentMember :
      finalSegment ∈ gridPolylineSegments route := by
    simpa [route, finalSegment] using
      finalCoordinatedSourceRoute_finalSegment_mem
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
  rcases
      finalCoordinatedSourceRoute_mem_namedDrawing
        formula
        clauseMember literalMember with
    ⟨routeIndex, routeMember⟩
  have targetDrawingPositionMember :
      placement.position targetAtom ∈
        drawing.vertexPositions := by
    change
      (finalCoordinatedPlacement formula).position targetAtom ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).vertexPositions
    exact
      finalCoordinatedSourceVariablePosition_mem_namedVertexPositions
        formula targetAtom targetAtomMember
  have verticesAvoid :
      drawing.VerticesAvoidRouteInteriors := by
    simpa only [drawing] using
      certificate.drawingRibbonReady.1.1.2
  exact
    verticesAvoidRouteInteriors_of_route_segment_mem
      drawing verticesAvoid targetDrawingPositionMember
      routeMember finalSegmentMember

/-- Source hypotheses instantiate final-segment interior avoidance. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_avoidsInterior_sourceVariablePosition
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
          (finalCoordinatedSource formula).erase) :
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    ¬finalSegment.InteriorContains
      ((finalCoordinatedPlacement formula).position
        targetAtom) := by
  exact
    finalCoordinatedSourceRoute_finalSegment_avoidsInterior_sourceVariablePosition_of_certificate
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      (retainedPlanarSATCertificate formula
        sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember targetAtom targetAtomMember

/-- Interior and endpoint avoidance together exclude all contact with a
segment. -/
theorem gridSegment_not_contains_of_avoidsInterior_and_endpoints
    {segment : GridSegment}
    {point : Cell}
    (avoidsInterior :
      ¬segment.InteriorContains point)
    (startDifferent :
      segment.start ≠ point)
    (finishDifferent :
      segment.finish ≠ point) :
    ¬segment.Contains point := by
  intro contains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        contains with
    interior | endpoint
  · exact avoidsInterior interior
  · rcases endpoint with atStart | atFinish
    · exact startDifferent atStart.symm
    · exact finishDifferent atFinish.symm

/-- The entrance endpoint of a genuine final source-route segment avoids
every source-variable base position at a different canonical center. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_start_ne_sourceVariablePosition
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
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    finalSegment.start ≠
      (finalCoordinatedPlacement formula).position
        targetAtom := by
  dsimp only
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let route := routes clauseIndex literalIndex
  have prefixAvoid :
      ∀ point ∈ route.dropLast,
        point ≠ placement.position targetAtom := by
    simpa [route, routes, placement] using
      (finalCoordinatedSourceRoutePrefix_avoids_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
        targetAtom targetAtomMember centersDifferent).1
  have routeLength : 2 ≤ route.length := by
    simpa [route, routes] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have reverseTailExists :
      ∃ entrance, route.reverse.tail.head? =
        some entrance :=
    exists_reverse_tail_head?_of_two_le_length
      route routeLength
  have entranceLast :
      route.dropLast.getLast? =
        some (polylineLastEntrance route) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have entranceMember :
      polylineLastEntrance route ∈ route.dropLast :=
    mem_of_getLast?_eq_some entranceLast
  exact
    prefixAvoid
      (polylineLastEntrance route)
      entranceMember

/-- The terminal endpoint of a genuine final source-route segment is its
canonical literal center, so it avoids any different source-variable
center. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_finish_ne_sourceVariablePosition
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
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        (finalCoordinatedPlacement formula).position
          targetAtom) :
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    finalSegment.finish ≠
      (finalCoordinatedPlacement formula).position
        targetAtom := by
  dsimp only
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let route := routes clauseIndex literalIndex
  have routeFinal :
      route.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement clause literal) := by
    simpa [route, routes, placement] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  have finalPointEq :
      route.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause literal := by
    simp [List.getLastD_eq_getLast?, routeFinal]
  rw [finalPointEq]
  exact centersDifferent

/-- The raw discarded final segment of a genuine fallback route is
axis-aligned and completely avoids every different occurring source
variable's base position. -/
theorem
    finalCoordinatedFallbackSourceRoute_finalSegment_avoids_sourceVariablePosition
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
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
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
    let route :=
      finalCoordinatedSourceRoutes
        formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route,
        route.getLastD (0, 0)⟩
    finalSegment.IsAxisAligned ∧
      ¬finalSegment.Contains
        ((finalCoordinatedPlacement formula).position
          targetAtom) := by
  dsimp only
  refine
    ⟨finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember choiceNone,
      ?_⟩
  apply
    gridSegment_not_contains_of_avoidsInterior_and_endpoints
  · exact
      finalCoordinatedSourceRoute_finalSegment_avoidsInterior_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
        targetAtom targetAtomMember
  · exact
      finalCoordinatedSourceRoute_finalSegment_start_ne_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
        targetAtom targetAtomMember centersDifferent
  · exact
      finalCoordinatedSourceRoute_finalSegment_finish_ne_sourceVariablePosition
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember literalMember
        targetAtom centersDifferent

end PeriodicOrthocrossing
end LeanTrominoes
