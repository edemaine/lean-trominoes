/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing

/-!
# Mapping finite embedded-CNF incidence drawings

Local incidence gadgets are most useful when one certified drawing can be
placed in several orientations.  This file isolates the exact hypotheses on
a point map needed to transport a complete finite drawing certificate:
injectivity, preservation of axis alignment, point/segment interior
incidence, and segment/segment interior incidence.

The resulting theorem is independent of any particular grid symmetry.
Translations and signed quarter-turns can instantiate it separately.
-/

namespace LeanTrominoes

/-- Apply a point map to both endpoints of a segment. -/
def GridSegment.mapPoints
    (transform : Cell → Cell) (segment : GridSegment) :
    GridSegment :=
  ⟨transform segment.start, transform segment.finish⟩

namespace PlanarThreeSAT

/-- The geometric facts needed to transport a continuously planar
orthogonal drawing through a point map. -/
structure GridDrawingMap (transform : Cell → Cell) : Prop where
  injective : Function.Injective transform
  isAxisAligned {segment : GridSegment} :
    segment.IsAxisAligned →
      (segment.mapPoints transform).IsAxisAligned
  interiorContains_iff {segment : GridSegment} {point : Cell} :
    (segment.mapPoints transform).InteriorContains (transform point) ↔
      segment.InteriorContains point
  interiorsMeet_iff {first second : GridSegment} :
    GridSegment.InteriorsMeet
        (first.mapPoints transform) (second.mapPoints transform) ↔
      GridSegment.InteriorsMeet first second

/-- Apply one point map to an embedded clause position. -/
def EmbeddedClause.mapPosition {Variable : Type*}
    (transform : Cell → Cell) (clause : EmbeddedClause Variable) :
    EmbeddedClause Variable where
  position := transform clause.position
  literals := clause.literals

/-- Apply one point map to the geometric part of incidence metadata. -/
def EmbeddedCNFIncidence.mapPosition {Variable : Type*}
    (transform : Cell → Cell)
    (incidence : EmbeddedCNFIncidence Variable) :
    EmbeddedCNFIncidence Variable where
  clause := incidence.clause.mapPosition transform
  clauseIndex := incidence.clauseIndex
  literal := incidence.literal
  literalIndex := incidence.literalIndex

/-- Apply one point map to every vertex and route point of a drawing. -/
def EmbeddedCNFIncidenceDrawing.mapPoints {Variable : Type*}
    (transform : Cell → Cell)
    (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    EmbeddedCNFIncidenceDrawing Variable where
  formula := drawing.formula.map
    (EmbeddedClause.mapPosition transform)
  variablePosition := fun atom =>
    transform (drawing.variablePosition atom)
  routes := fun clauseIndex literalIndex =>
    (drawing.routes clauseIndex literalIndex).map transform

namespace EmbeddedCNFIncidenceDrawing

/-- Segment formation commutes with mapping every polyline point. -/
theorem gridPolylineSegments_map_points
    (transform : Cell → Cell) (points : List Cell) :
    gridPolylineSegments (points.map transform) =
      (gridPolylineSegments points).map
        (GridSegment.mapPoints transform) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      rfl
  | cons_cons first second rest _ induction =>
      simp only [List.map_cons, gridPolylineSegments]
      congr 1
      exact induction second

/-- Mapping clause positions preserves the ordered incidence presentation. -/
theorem incidences_mapPoints
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).incidences =
      drawing.incidences.map
        (EmbeddedCNFIncidence.mapPosition transform) := by
  unfold incidences embeddedCNFIncidences
  rw [show (drawing.mapPoints transform).formula =
      drawing.formula.map
        (EmbeddedClause.mapPosition transform) by rfl,
    List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  simp [EmbeddedCNFIncidence.mapPosition,
    EmbeddedClause.mapPosition, List.map_map,
    Function.comp_def]

@[simp]
theorem mapPoints_incidences_length
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).incidences.length =
      drawing.incidences.length := by
  rw [incidences_mapPoints]
  simp

/-- A mapped drawing selects the mapped incidence at the same finite
presentation index. -/
theorem incidenceAt_mapPoints
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell)
    (index : Fin (drawing.mapPoints transform).incidences.length) :
    let originalIndex : Fin drawing.incidences.length :=
      ⟨index.val, by
        exact index.isLt.trans_eq
          (mapPoints_incidences_length drawing transform)⟩
    (drawing.mapPoints transform).incidenceAt index =
      (drawing.incidenceAt originalIndex).mapPosition transform := by
  intro originalIndex
  unfold incidenceAt
  have lookup := congrArg
    (fun incidences => incidences[index.val]?)
    (incidences_mapPoints drawing transform)
  rw [List.getElem?_eq_getElem index.isLt,
    List.getElem?_map,
    List.getElem?_eq_getElem originalIndex.isLt] at lookup
  exact Option.some.inj lookup

/-- The selected route of mapped incidence metadata is the pointwise map of
the original selected route. -/
theorem routeAt_mapPoints_incidence
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell)
    (incidence : EmbeddedCNFIncidence Variable) :
    (drawing.mapPoints transform).routeAt
        (incidence.mapPosition transform) =
      (drawing.routeAt incidence).map transform := by
  rfl

/-- Mapping positions changes no logical variable enumeration. -/
theorem variableVertices_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).variableVertices =
      drawing.variableVertices := by
  unfold variableVertices
  simp [EmbeddedCNFIncidenceDrawing.mapPoints,
    EmbeddedClause.mapPosition, List.flatMap_map]

/-- The mapped vertex list is exactly the pointwise image of the original
vertex list. -/
theorem vertexPositions_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).vertexPositions =
      drawing.vertexPositions.map transform := by
  simp [vertexPositions, variableVertices,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    EmbeddedClause.mapPosition, List.map_append,
    List.flatMap_map, List.map_map, Function.comp_def]

@[simp]
theorem mapPoints_vertexPositions_length
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).vertexPositions.length =
      drawing.vertexPositions.length := by
  rw [vertexPositions_mapPoints]
  simp

/-- Route simplicity is preserved by any certified drawing map. -/
theorem routeIsSimple_mapPoints
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    {route : List Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route) :
    LocalIncidenceDrawing.RouteIsSimple (route.map transform) := by
  rcases simple with ⟨nodup, pointsAvoid, segmentsAvoid⟩
  constructor
  · exact nodup.map geometry.injective
  constructor
  · intro mappedPoint mappedPointMember mappedSegment mappedSegmentMember
      contains
    rcases List.mem_map.mp mappedPointMember with
      ⟨point, pointMember, rfl⟩
    rw [gridPolylineSegments_map_points] at mappedSegmentMember
    rcases List.mem_map.mp mappedSegmentMember with
      ⟨segment, segmentMember, rfl⟩
    exact pointsAvoid point pointMember segment segmentMember
      (geometry.interiorContains_iff.mp contains)
  · intro mappedFirst mappedFirstMember mappedSecond mappedSecondMember
      indicesDifferent meet
    rw [gridPolylineSegments_map_points, List.zipIdx_map]
      at mappedFirstMember mappedSecondMember
    rcases List.mem_map.mp mappedFirstMember with
      ⟨first, firstMember, firstEqual⟩
    rcases List.mem_map.mp mappedSecondMember with
      ⟨second, secondMember, secondEqual⟩
    have firstIndexEqual : first.2 = mappedFirst.2 :=
      by simpa using congrArg Prod.snd firstEqual
    have secondIndexEqual : second.2 = mappedSecond.2 :=
      by simpa using congrArg Prod.snd secondEqual
    apply segmentsAvoid first firstMember second secondMember
    · simpa [firstIndexEqual, secondIndexEqual] using indicesDifferent
    · have firstSegmentEqual :
          first.1.mapPoints transform = mappedFirst.1 :=
        congrArg Prod.fst firstEqual
      have secondSegmentEqual :
          second.1.mapPoints transform = mappedSecond.1 :=
        congrArg Prod.fst secondEqual
      rw [← firstSegmentEqual, ← secondSegmentEqual] at meet
      exact geometry.interiorsMeet_iff.mp meet

/-- Continuous segment separation is preserved by a certified drawing map. -/
theorem segmentInteriorsDisjoint_mapPoints
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    {first second : List Cell}
    (disjoint : SegmentInteriorsDisjoint first second) :
    SegmentInteriorsDisjoint
      (first.map transform) (second.map transform) := by
  intro mappedFirstIndex mappedSecondIndex meet
  let firstIndex : Fin (gridPolylineSegments first).length :=
    ⟨mappedFirstIndex.val, by
      simpa [gridPolylineSegments_map_points] using
        mappedFirstIndex.isLt⟩
  let secondIndex : Fin (gridPolylineSegments second).length :=
    ⟨mappedSecondIndex.val, by
      simpa [gridPolylineSegments_map_points] using
        mappedSecondIndex.isLt⟩
  apply disjoint firstIndex secondIndex
  have firstGet :
      (gridPolylineSegments (first.map transform)).get
          mappedFirstIndex =
        ((gridPolylineSegments first).get firstIndex).mapPoints
          transform := by
    simp [gridPolylineSegments_map_points, firstIndex]
  have secondGet :
      (gridPolylineSegments (second.map transform)).get
          mappedSecondIndex =
        ((gridPolylineSegments second).get secondIndex).mapPoints
          transform := by
    simp [gridPolylineSegments_map_points, secondIndex]
  rw [firstGet, secondGet] at meet
  exact geometry.interiorsMeet_iff.mp meet

/-- Listed-point avoidance of route interiors is preserved by a certified
drawing map. -/
theorem routePointsAvoidInteriors_mapPoints
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    {first second : List Cell}
    (avoids : RoutePointsAvoidInteriors first second) :
    RoutePointsAvoidInteriors
      (first.map transform) (second.map transform) := by
  intro mappedPointIndex mappedSegmentIndex contains
  let pointIndex : Fin first.length :=
    ⟨mappedPointIndex.val, by
      simpa using mappedPointIndex.isLt⟩
  let segmentIndex :
      Fin (gridPolylineSegments second).length :=
    ⟨mappedSegmentIndex.val, by
      simpa [gridPolylineSegments_map_points] using
        mappedSegmentIndex.isLt⟩
  apply avoids pointIndex segmentIndex
  have pointGet :
      (first.map transform).get mappedPointIndex =
        transform (first.get pointIndex) := by
    simp [pointIndex]
  have segmentGet :
      (gridPolylineSegments (second.map transform)).get
          mappedSegmentIndex =
        ((gridPolylineSegments second).get segmentIndex).mapPoints
          transform := by
    simp [gridPolylineSegments_map_points, segmentIndex]
  rw [pointGet, segmentGet] at contains
  exact geometry.interiorContains_iff.mp contains

/-- Endpoint-only listed contacts are preserved by an injective point map. -/
theorem routesMeetOnlyAtEndpoints_mapPoints
    {transform : Cell → Cell}
    (injective : Function.Injective transform)
    {first second : List Cell}
    (onlyEndpoints : RoutesMeetOnlyAtEndpoints first second) :
    RoutesMeetOnlyAtEndpoints
      (first.map transform) (second.map transform) := by
  intro mappedFirstIndex mappedSecondIndex pointsEqual
  let firstIndex : Fin first.length :=
    ⟨mappedFirstIndex.val, by
      simpa using mappedFirstIndex.isLt⟩
  let secondIndex : Fin second.length :=
    ⟨mappedSecondIndex.val, by
      simpa using mappedSecondIndex.isLt⟩
  have firstGet :
      (first.map transform).get mappedFirstIndex =
        transform (first.get firstIndex) := by
    simp [firstIndex]
  have secondGet :
      (second.map transform).get mappedSecondIndex =
        transform (second.get secondIndex) := by
    simp [secondIndex]
  rw [firstGet, secondGet] at pointsEqual
  have base :=
    onlyEndpoints firstIndex secondIndex
      (injective pointsEqual)
  constructor
  · rcases base.1 with firstHead | firstLast
    · left
      simp only [List.head?_map, firstHead, Option.map_some]
      exact congrArg some firstGet.symm
    · right
      simp only [List.getLast?_map, firstLast, Option.map_some]
      exact congrArg some firstGet.symm
  · rcases base.2 with secondHead | secondLast
    · left
      simp only [List.head?_map, secondHead, Option.map_some]
      exact congrArg some secondGet.symm
    · right
      simp only [List.getLast?_map, secondLast, Option.map_some]
      exact congrArg some secondGet.symm

/-- Complete pairwise route separation is preserved by a certified drawing
map. -/
theorem routesAvoidEachOther_mapPoints
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    {first second : List Cell}
    (avoids : RoutesAvoidEachOther first second) :
    RoutesAvoidEachOther
      (first.map transform) (second.map transform) :=
  ⟨segmentInteriorsDisjoint_mapPoints geometry avoids.1,
    routePointsAvoidInteriors_mapPoints geometry avoids.2.1,
    routePointsAvoidInteriors_mapPoints geometry avoids.2.2.1,
    routesMeetOnlyAtEndpoints_mapPoints
      geometry.injective avoids.2.2.2⟩

/-- Exact route endpoints are preserved by any point map. -/
theorem routesMatch_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (routesMatch : drawing.RoutesMatch)
    (transform : Cell → Cell) :
    (drawing.mapPoints transform).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  change
    (clause, clauseIndex) ∈
      (drawing.formula.map
        (EmbeddedClause.mapPosition transform)).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  have indexEqual : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have clauseEqual :
      clause =
        EmbeddedClause.mapPosition transform taggedClause.1 :=
    (congrArg Prod.fst taggedClauseEqual).symm
  subst clauseIndex
  subst clause
  have base :=
    EmbeddedCNFIncidenceDrawing.physicalRoutesMatch
      drawing routesMatch
      taggedClause.1 taggedClause.2 taggedClauseMember
      literal literalIndex literalMember
  change
    ((drawing.routes taggedClause.2 literalIndex).map
        transform).head? =
        some (transform taggedClause.1.position) ∧
      ((drawing.routes taggedClause.2 literalIndex).map
        transform).getLast? =
        some (transform
          (drawing.variablePosition literal.1))
  simp only [List.head?_map, List.getLast?_map,
    base.1, base.2, Option.map_some]
  exact ⟨True.intro, True.intro⟩

/-- Orthogonality is preserved by a certified drawing map. -/
theorem isOrthogonal_mapPoints
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    (orthogonal : drawing.IsOrthogonal) :
    (drawing.mapPoints transform).IsOrthogonal := by
  intro mappedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨mappedIndex.val, by
      exact mappedIndex.isLt.trans_eq
        (mapPoints_incidences_length drawing transform)⟩
  have incidenceEqual :=
    incidenceAt_mapPoints drawing transform mappedIndex
  change
    ∀ segmentIndex :
        Fin (gridPolylineSegments
          ((drawing.mapPoints transform).routeAt
            ((drawing.mapPoints transform).incidenceAt
              mappedIndex))).length,
      ((gridPolylineSegments
        ((drawing.mapPoints transform).routeAt
          ((drawing.mapPoints transform).incidenceAt
            mappedIndex))).get segmentIndex).IsAxisAligned
  rw [incidenceEqual, routeAt_mapPoints_incidence,
    gridPolylineSegments_map_points]
  intro mappedSegmentIndex
  let originalSegmentIndex :
      Fin (gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIndex))).length :=
    ⟨mappedSegmentIndex.val, by
      simpa using mappedSegmentIndex.isLt⟩
  have base := orthogonal originalIndex originalSegmentIndex
  have getEqual :
      ((gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIndex))).map
          (GridSegment.mapPoints transform)).get
          mappedSegmentIndex =
        ((gridPolylineSegments
          (drawing.routeAt
            (drawing.incidenceAt originalIndex))).get
          originalSegmentIndex).mapPoints transform := by
    simp [originalSegmentIndex]
  rw [getEqual]
  exact geometry.isAxisAligned base

/-- Vertex avoidance of route interiors is preserved by a certified drawing
map. -/
theorem verticesAvoidRouteInteriors_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    (avoids : drawing.VerticesAvoidRouteInteriors) :
    (drawing.mapPoints transform).VerticesAvoidRouteInteriors := by
  intro mappedVertexIndex mappedIncidenceIndex
  let originalVertexIndex :
      Fin drawing.vertexPositions.length :=
    ⟨mappedVertexIndex.val,
      mappedVertexIndex.isLt.trans_eq
        (mapPoints_vertexPositions_length drawing transform)⟩
  let originalIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨mappedIncidenceIndex.val,
      mappedIncidenceIndex.isLt.trans_eq
        (mapPoints_incidences_length drawing transform)⟩
  have incidenceEqual :=
    incidenceAt_mapPoints drawing transform mappedIncidenceIndex
  change
    ∀ mappedSegmentIndex :
        Fin (gridPolylineSegments
          ((drawing.mapPoints transform).routeAt
            ((drawing.mapPoints transform).incidenceAt
              mappedIncidenceIndex))).length,
      ¬((gridPolylineSegments
          ((drawing.mapPoints transform).routeAt
            ((drawing.mapPoints transform).incidenceAt
              mappedIncidenceIndex))).get
          mappedSegmentIndex).InteriorContains
        ((drawing.mapPoints transform).vertexPositions.get
          mappedVertexIndex)
  rw [incidenceEqual, routeAt_mapPoints_incidence,
    gridPolylineSegments_map_points]
  intro mappedSegmentIndex contains
  let originalSegmentIndex :
      Fin (gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIncidenceIndex))).length :=
    ⟨mappedSegmentIndex.val, by
      simpa using mappedSegmentIndex.isLt⟩
  apply avoids originalVertexIndex originalIncidenceIndex
    originalSegmentIndex
  have vertexGet :
      (drawing.mapPoints transform).vertexPositions.get
          mappedVertexIndex =
        transform
          (drawing.vertexPositions.get originalVertexIndex) := by
    have lookup := congrArg
      (fun positions => positions[mappedVertexIndex.val]?)
      (vertexPositions_mapPoints drawing transform)
    rw [List.getElem?_eq_getElem mappedVertexIndex.isLt,
      List.getElem?_map,
      List.getElem?_eq_getElem originalVertexIndex.isLt]
      at lookup
    exact Option.some.inj lookup
  have segmentGet :
      ((gridPolylineSegments
          (drawing.routeAt
            (drawing.incidenceAt originalIncidenceIndex))).map
          (GridSegment.mapPoints transform)).get
          mappedSegmentIndex =
        ((gridPolylineSegments
          (drawing.routeAt
            (drawing.incidenceAt originalIncidenceIndex))).get
          originalSegmentIndex).mapPoints transform := by
    simp [originalSegmentIndex]
  rw [segmentGet, vertexGet] at contains
  exact geometry.interiorContains_iff.mp contains

/-- Continuous planarity is preserved by a certified drawing map. -/
theorem isPlanar_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    (planar : drawing.IsPlanar) :
    (drawing.mapPoints transform).IsPlanar := by
  rcases planar with
    ⟨routesSimple, routesAvoid, verticesAvoid, verticesNodup⟩
  constructor
  · intro mappedIndex
    let originalIndex : Fin drawing.incidences.length :=
      ⟨mappedIndex.val,
        mappedIndex.isLt.trans_eq
          (mapPoints_incidences_length drawing transform)⟩
    have incidenceEqual :=
      incidenceAt_mapPoints drawing transform mappedIndex
    rw [incidenceEqual, routeAt_mapPoints_incidence]
    exact routeIsSimple_mapPoints geometry
      (routesSimple originalIndex)
  constructor
  · intro mappedFirstIndex mappedSecondIndex mappedDifferent
    let originalFirstIndex : Fin drawing.incidences.length :=
      ⟨mappedFirstIndex.val,
        mappedFirstIndex.isLt.trans_eq
          (mapPoints_incidences_length drawing transform)⟩
    let originalSecondIndex : Fin drawing.incidences.length :=
      ⟨mappedSecondIndex.val,
        mappedSecondIndex.isLt.trans_eq
          (mapPoints_incidences_length drawing transform)⟩
    have originalDifferent :
        originalFirstIndex ≠ originalSecondIndex := by
      intro equal
      apply mappedDifferent
      apply Fin.ext
      simpa [originalFirstIndex, originalSecondIndex] using
        congrArg Fin.val equal
    have firstIncidenceEqual :=
      incidenceAt_mapPoints drawing transform mappedFirstIndex
    have secondIncidenceEqual :=
      incidenceAt_mapPoints drawing transform mappedSecondIndex
    rw [firstIncidenceEqual, secondIncidenceEqual,
      routeAt_mapPoints_incidence,
      routeAt_mapPoints_incidence]
    exact routesAvoidEachOther_mapPoints geometry
      (routesAvoid originalFirstIndex originalSecondIndex
        originalDifferent)
  constructor
  · exact verticesAvoidRouteInteriors_mapPoints
      geometry verticesAvoid
  · rw [vertexPositions_mapPoints]
    exact verticesNodup.map geometry.injective

/-- A complete embedded-CNF drawing certificate transports through any
certified grid drawing map. -/
theorem isValid_mapPoints
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {transform : Cell → Cell}
    (geometry : GridDrawingMap transform)
    (valid : drawing.IsValid) :
    (drawing.mapPoints transform).IsValid :=
  ⟨routesMatch_mapPoints valid.1 transform,
    isOrthogonal_mapPoints geometry valid.2.1,
    isPlanar_mapPoints geometry valid.2.2⟩

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
