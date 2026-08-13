/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity
import LeanTrominoes.PeriodicGridDrawingFinitePlanarity

/-!
# Translating finite embedded-CNF incidence drawings

Local SAT gadgets are certified once in fixed coordinates and then placed
at many input-dependent macrocell origins.  This module proves that a common
integer translation of every clause vertex, variable vertex, and route point
preserves the complete finite drawing certificate.

The proof transports exact endpoints, axis alignment, route simplicity,
continuous separation of distinct routes, vertex avoidance, and distinct
vertex positions.  The final `isValid_translate` theorem lets later
constructions reuse a constant local certificate at arbitrary origins.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

def EmbeddedClause.translate {Variable : Type*}
    (offset : Cell) (clause : EmbeddedClause Variable) :
    EmbeddedClause Variable where
  position := Cell.add offset clause.position
  literals := clause.literals

def EmbeddedCNFIncidence.translate {Variable : Type*}
    (offset : Cell) (incidence : EmbeddedCNFIncidence Variable) :
    EmbeddedCNFIncidence Variable where
  clause := incidence.clause.translate offset
  clauseIndex := incidence.clauseIndex
  literal := incidence.literal
  literalIndex := incidence.literalIndex

def EmbeddedCNFIncidenceDrawing.translate {Variable : Type*}
    (offset : Cell)
  (drawing : EmbeddedCNFIncidenceDrawing Variable) :
    EmbeddedCNFIncidenceDrawing Variable where
  formula := drawing.formula.map (EmbeddedClause.translate offset)
  variablePosition := fun atom =>
    Cell.add offset (drawing.variablePosition atom)
  routes := fun clauseIndex literalIndex =>
    (drawing.routes clauseIndex literalIndex).map
      (Cell.add offset)

namespace EmbeddedCNFIncidenceDrawing

theorem cell_add_left_injective (offset : Cell) :
    Function.Injective (Cell.add offset) := by
  intro first second equal
  apply Prod.ext
  · have := congrArg Prod.fst equal
    simpa [Cell.add] using this
  · have := congrArg Prod.snd equal
    simpa [Cell.add] using this

theorem gridPolylineSegments_map_add
    (points : List Cell) (offset : Cell) :
    gridPolylineSegments
        (points.map (Cell.add offset)) =
      (gridPolylineSegments points).map
        (GridSegment.translate offset) := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      rfl
  | cons_cons first second rest _ induction =>
      simp only [List.map_cons, gridPolylineSegments,
        List.map_cons]
      congr 1
      exact induction second

theorem routeIsSimple_translate
    {route : List Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (offset : Cell) :
    LocalIncidenceDrawing.RouteIsSimple
      (route.map (Cell.add offset)) := by
  rcases simple with
    ⟨nodup, pointsAvoid, segmentsAvoid⟩
  constructor
  · exact nodup.map (cell_add_left_injective offset)
  constructor
  · intro translatedPoint translatedPointMember
      translatedSegment translatedSegmentMember contains
    rcases List.mem_map.mp translatedPointMember with
      ⟨point, pointMember, rfl⟩
    rw [gridPolylineSegments_map_add] at translatedSegmentMember
    rcases List.mem_map.mp translatedSegmentMember with
      ⟨segment, segmentMember, rfl⟩
    apply pointsAvoid point pointMember segment segmentMember
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        segment offset point).mp
        (by simpa [Cell.add, add_comm] using contains)
  · intro translatedFirst translatedFirstMember
      translatedSecond translatedSecondMember indicesDifferent meet
    rw [gridPolylineSegments_map_add, List.zipIdx_map]
      at translatedFirstMember translatedSecondMember
    rcases List.mem_map.mp translatedFirstMember with
      ⟨first, firstMember, firstEqual⟩
    rcases List.mem_map.mp translatedSecondMember with
      ⟨second, secondMember, secondEqual⟩
    have firstIndexEqual :
        first.2 = translatedFirst.2 :=
      by simpa using congrArg Prod.snd firstEqual
    have secondIndexEqual :
        second.2 = translatedSecond.2 :=
      by simpa using congrArg Prod.snd secondEqual
    have originalIndicesDifferent :
        first.2 ≠ second.2 := by
      simpa [firstIndexEqual, secondIndexEqual] using indicesDifferent
    apply segmentsAvoid first firstMember second secondMember
      originalIndicesDifferent
    have segmentEqual :
        GridSegment.translate offset first.1 =
          translatedFirst.1 :=
      congrArg Prod.fst firstEqual
    have secondSegmentEqual :
        GridSegment.translate offset second.1 =
          translatedSecond.1 :=
      congrArg Prod.fst secondEqual
    rw [← segmentEqual, ← secondSegmentEqual] at meet
    exact
      (GridSegment.interiorsMeet_translate_both_iff
        first.1 second.1 offset).mp meet

theorem segmentInteriorsDisjoint_translate
    {first second : List Cell}
    (disjoint :
      SegmentInteriorsDisjoint first second)
    (offset : Cell) :
    SegmentInteriorsDisjoint
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) := by
  intro translatedFirstIndex translatedSecondIndex meet
  let firstIndex :
      Fin (gridPolylineSegments first).length :=
    ⟨translatedFirstIndex.val, by
      simpa [gridPolylineSegments_map_add] using
        translatedFirstIndex.isLt⟩
  let secondIndex :
      Fin (gridPolylineSegments second).length :=
    ⟨translatedSecondIndex.val, by
      simpa [gridPolylineSegments_map_add] using
        translatedSecondIndex.isLt⟩
  apply disjoint firstIndex secondIndex
  have firstGet :
      (gridPolylineSegments
          (first.map (Cell.add offset))).get
          translatedFirstIndex =
        GridSegment.translate offset
          ((gridPolylineSegments first).get firstIndex) := by
    simp [gridPolylineSegments_map_add, firstIndex]
  have secondGet :
      (gridPolylineSegments
          (second.map (Cell.add offset))).get
          translatedSecondIndex =
        GridSegment.translate offset
          ((gridPolylineSegments second).get secondIndex) := by
    simp [gridPolylineSegments_map_add, secondIndex]
  rw [firstGet, secondGet] at meet
  exact
    (GridSegment.interiorsMeet_translate_both_iff
      ((gridPolylineSegments first).get firstIndex)
      ((gridPolylineSegments second).get secondIndex)
      offset).mp meet

theorem routePointsAvoidInteriors_translate
    {first second : List Cell}
    (avoids : RoutePointsAvoidInteriors first second)
    (offset : Cell) :
    RoutePointsAvoidInteriors
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) := by
  intro translatedPointIndex translatedSegmentIndex contains
  let pointIndex : Fin first.length :=
    ⟨translatedPointIndex.val, by
      simpa using translatedPointIndex.isLt⟩
  let segmentIndex :
      Fin (gridPolylineSegments second).length :=
    ⟨translatedSegmentIndex.val, by
      simpa [gridPolylineSegments_map_add] using
        translatedSegmentIndex.isLt⟩
  apply avoids pointIndex segmentIndex
  have pointGet :
      (first.map (Cell.add offset)).get
          translatedPointIndex =
        Cell.add offset (first.get pointIndex) := by
    simp [pointIndex]
  have segmentGet :
      (gridPolylineSegments
          (second.map (Cell.add offset))).get
          translatedSegmentIndex =
        GridSegment.translate offset
          ((gridPolylineSegments second).get segmentIndex) := by
    simp [gridPolylineSegments_map_add, segmentIndex]
  rw [pointGet, segmentGet] at contains
  exact
    (PeriodicGridDrawing.interiorContains_translate_iff
      ((gridPolylineSegments second).get segmentIndex)
      offset (first.get pointIndex)).mp
      (by simpa [Cell.add, add_comm] using contains)

theorem routesMeetOnlyAtEndpoints_translate
    {first second : List Cell}
    (onlyEndpoints :
      RoutesMeetOnlyAtEndpoints first second)
    (offset : Cell) :
    RoutesMeetOnlyAtEndpoints
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) := by
  intro translatedFirstIndex translatedSecondIndex pointsEqual
  let firstIndex : Fin first.length :=
    ⟨translatedFirstIndex.val, by
      simpa using translatedFirstIndex.isLt⟩
  let secondIndex : Fin second.length :=
    ⟨translatedSecondIndex.val, by
      simpa using translatedSecondIndex.isLt⟩
  have firstGet :
      (first.map (Cell.add offset)).get
          translatedFirstIndex =
        Cell.add offset (first.get firstIndex) := by
    simp [firstIndex]
  have secondGet :
      (second.map (Cell.add offset)).get
          translatedSecondIndex =
        Cell.add offset (second.get secondIndex) := by
    simp [secondIndex]
  rw [firstGet, secondGet] at pointsEqual
  have originalPointsEqual :
      first.get firstIndex = second.get secondIndex :=
    cell_add_left_injective offset pointsEqual
  have base :=
    onlyEndpoints firstIndex secondIndex originalPointsEqual
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

theorem routesAvoidEachOther_translate
    {first second : List Cell}
    (avoids : RoutesAvoidEachOther first second)
    (offset : Cell) :
    RoutesAvoidEachOther
      (first.map (Cell.add offset))
      (second.map (Cell.add offset)) :=
  ⟨segmentInteriorsDisjoint_translate avoids.1 offset,
    routePointsAvoidInteriors_translate avoids.2.1 offset,
    routePointsAvoidInteriors_translate avoids.2.2.1 offset,
    routesMeetOnlyAtEndpoints_translate avoids.2.2.2 offset⟩

theorem routeAt_translate_incidence
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (incidence : EmbeddedCNFIncidence Variable)
    (offset : Cell) :
    (drawing.translate offset).routeAt
        (incidence.translate offset) =
      (drawing.routeAt incidence).map (Cell.add offset) := by
  rfl

theorem incidences_translate {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell) :
    (drawing.translate offset).incidences =
      drawing.incidences.map
        (EmbeddedCNFIncidence.translate offset) := by
  unfold incidences embeddedCNFIncidences
  rw [show (drawing.translate offset).formula =
      drawing.formula.map (EmbeddedClause.translate offset) by rfl,
    List.zipIdx_map, List.flatMap_map]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  simp [EmbeddedCNFIncidence.translate,
    EmbeddedClause.translate, List.map_map,
    Function.comp_def]

/-- Translating a drawing changes vertex coordinates but not the ordered
list of logical variables occurring in its formula. -/
theorem variableVertices_translate
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell) :
    (drawing.translate offset).variableVertices =
      drawing.variableVertices := by
  unfold variableVertices
  simp [EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate, List.flatMap_map]

@[simp]
theorem translate_incidences_length {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell) :
    (drawing.translate offset).incidences.length =
      drawing.incidences.length := by
  rw [incidences_translate]
  simp

theorem vertexPositions_translate
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell) :
    (drawing.translate offset).vertexPositions =
      drawing.vertexPositions.map (Cell.add offset) := by
  simp [vertexPositions, variableVertices,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate, List.map_append,
    List.flatMap_map, List.map_map, Function.comp_def]

@[simp]
theorem translate_vertexPositions_length
    {Variable : Type*} [DecidableEq Variable]
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell) :
    (drawing.translate offset).vertexPositions.length =
      drawing.vertexPositions.length := by
  rw [vertexPositions_translate]
  simp

theorem routesMatch_translate
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (routesMatch : drawing.RoutesMatch)
    (offset : Cell) :
    (drawing.translate offset).RoutesMatch := by
  apply EmbeddedCNFIncidenceDrawing.routesMatch_of_physical
  intro clause clauseIndex clauseMember
    literal literalIndex literalMember
  change
    (clause, clauseIndex) ∈
      (drawing.formula.map
        (EmbeddedClause.translate offset)).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, taggedClauseEqual⟩
  have indexEqual :
      taggedClause.2 = clauseIndex :=
    congrArg Prod.snd taggedClauseEqual
  have clauseEqual :
      clause =
        EmbeddedClause.translate offset taggedClause.1 :=
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
        (Cell.add offset)).head? =
        some (Cell.add offset taggedClause.1.position) ∧
      ((drawing.routes taggedClause.2 literalIndex).map
        (Cell.add offset)).getLast? =
        some (Cell.add offset
          (drawing.variablePosition literal.1))
  simp only [List.head?_map, List.getLast?_map,
    base.1, base.2, Option.map_some]
  exact ⟨True.intro, True.intro⟩

theorem incidenceAt_translate
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (offset : Cell)
    (index :
      Fin (drawing.translate offset).incidences.length) :
    let originalIndex : Fin drawing.incidences.length :=
      ⟨index.val, by
        exact index.isLt.trans_eq
          (translate_incidences_length drawing offset)⟩
    (drawing.translate offset).incidenceAt index =
      (drawing.incidenceAt originalIndex).translate offset := by
  intro originalIndex
  unfold incidenceAt
  have lookup := congrArg
    (fun incidences =>
      incidences[index.val]?)
    (incidences_translate drawing offset)
  rw [List.getElem?_eq_getElem index.isLt,
    List.getElem?_map,
    List.getElem?_eq_getElem originalIndex.isLt]
    at lookup
  exact Option.some.inj lookup

theorem isOrthogonal_translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (orthogonal : drawing.IsOrthogonal)
    (offset : Cell) :
    (drawing.translate offset).IsOrthogonal := by
  intro translatedIndex
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  change
    ∀ segmentIndex :
        Fin (gridPolylineSegments
          ((drawing.translate offset).routeAt
            ((drawing.translate offset).incidenceAt
              translatedIndex))).length,
      ((gridPolylineSegments
        ((drawing.translate offset).routeAt
          ((drawing.translate offset).incidenceAt
            translatedIndex))).get segmentIndex).IsAxisAligned
  rw [incidenceEqual,
    routeAt_translate_incidence,
    gridPolylineSegments_map_add]
  intro translatedSegmentIndex
  let originalSegmentIndex :
      Fin (gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIndex))).length :=
    ⟨translatedSegmentIndex.val, by
      simpa using translatedSegmentIndex.isLt⟩
  have base := orthogonal originalIndex originalSegmentIndex
  simpa [originalSegmentIndex,
    GridSegment.isAxisAligned_translate] using base

theorem verticesAvoidRouteInteriors_translate
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (avoids : drawing.VerticesAvoidRouteInteriors)
    (offset : Cell) :
    (drawing.translate offset).VerticesAvoidRouteInteriors := by
  intro translatedVertexIndex translatedIncidenceIndex
  let originalVertexIndex :
      Fin drawing.vertexPositions.length :=
    ⟨translatedVertexIndex.val,
      translatedVertexIndex.isLt.trans_eq
        (translate_vertexPositions_length drawing offset)⟩
  let originalIncidenceIndex :
      Fin drawing.incidences.length :=
    ⟨translatedIncidenceIndex.val,
      translatedIncidenceIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIncidenceIndex
  change
    ∀ translatedSegmentIndex :
        Fin (gridPolylineSegments
          ((drawing.translate offset).routeAt
            ((drawing.translate offset).incidenceAt
              translatedIncidenceIndex))).length,
      ¬((gridPolylineSegments
          ((drawing.translate offset).routeAt
            ((drawing.translate offset).incidenceAt
              translatedIncidenceIndex))).get
          translatedSegmentIndex).InteriorContains
        ((drawing.translate offset).vertexPositions.get
          translatedVertexIndex)
  rw [incidenceEqual, routeAt_translate_incidence,
    gridPolylineSegments_map_add]
  intro translatedSegmentIndex contains
  let originalSegmentIndex :
      Fin (gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIncidenceIndex))).length :=
    ⟨translatedSegmentIndex.val, by
      simpa using translatedSegmentIndex.isLt⟩
  apply avoids originalVertexIndex originalIncidenceIndex
    originalSegmentIndex
  have vertexGet :
      (drawing.translate offset).vertexPositions.get
          translatedVertexIndex =
        Cell.add offset
          (drawing.vertexPositions.get originalVertexIndex) := by
    have lookup := congrArg
      (fun positions => positions[translatedVertexIndex.val]?)
      (vertexPositions_translate drawing offset)
    rw [List.getElem?_eq_getElem translatedVertexIndex.isLt,
      List.getElem?_map,
      List.getElem?_eq_getElem originalVertexIndex.isLt]
      at lookup
    exact Option.some.inj lookup
  have segmentGet :
      ((gridPolylineSegments
          (drawing.routeAt
            (drawing.incidenceAt originalIncidenceIndex))).map
          (GridSegment.translate offset)).get
          translatedSegmentIndex =
        GridSegment.translate offset
          ((gridPolylineSegments
            (drawing.routeAt
              (drawing.incidenceAt originalIncidenceIndex))).get
            originalSegmentIndex) := by
    simp [originalSegmentIndex]
  rw [segmentGet, vertexGet] at contains
  exact
    (PeriodicGridDrawing.interiorContains_translate_iff
      ((gridPolylineSegments
        (drawing.routeAt
          (drawing.incidenceAt originalIncidenceIndex))).get
        originalSegmentIndex)
      offset
      (drawing.vertexPositions.get originalVertexIndex)).mp
      (by simpa [Cell.add, add_comm] using contains)

theorem isPlanar_translate
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (planar : drawing.IsPlanar)
    (offset : Cell) :
    (drawing.translate offset).IsPlanar := by
  rcases planar with
    ⟨routesSimple, routesAvoid, verticesAvoid, verticesNodup⟩
  constructor
  · intro translatedIndex
    let originalIndex : Fin drawing.incidences.length :=
      ⟨translatedIndex.val,
        translatedIndex.isLt.trans_eq
          (translate_incidences_length drawing offset)⟩
    have incidenceEqual :=
      incidenceAt_translate drawing offset translatedIndex
    rw [incidenceEqual, routeAt_translate_incidence]
    exact routeIsSimple_translate
      (routesSimple originalIndex) offset
  constructor
  · intro translatedFirstIndex translatedSecondIndex
      translatedDifferent
    let originalFirstIndex : Fin drawing.incidences.length :=
      ⟨translatedFirstIndex.val,
        translatedFirstIndex.isLt.trans_eq
          (translate_incidences_length drawing offset)⟩
    let originalSecondIndex : Fin drawing.incidences.length :=
      ⟨translatedSecondIndex.val,
        translatedSecondIndex.isLt.trans_eq
          (translate_incidences_length drawing offset)⟩
    have originalDifferent :
        originalFirstIndex ≠ originalSecondIndex := by
      intro equal
      apply translatedDifferent
      have values :
          translatedFirstIndex.val =
            translatedSecondIndex.val := by
        simpa [originalFirstIndex, originalSecondIndex] using
          congrArg Fin.val equal
      exact Fin.ext values
    have firstIncidenceEqual :=
      incidenceAt_translate drawing offset translatedFirstIndex
    have secondIncidenceEqual :=
      incidenceAt_translate drawing offset translatedSecondIndex
    rw [firstIncidenceEqual, secondIncidenceEqual,
      routeAt_translate_incidence,
      routeAt_translate_incidence]
    exact routesAvoidEachOther_translate
      (routesAvoid originalFirstIndex originalSecondIndex
        originalDifferent)
      offset
  constructor
  · exact verticesAvoidRouteInteriors_translate
      verticesAvoid offset
  · rw [vertexPositions_translate]
    exact verticesNodup.map
      (cell_add_left_injective offset)

theorem isValid_translate
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (valid : drawing.IsValid)
    (offset : Cell) :
    (drawing.translate offset).IsValid :=
  ⟨routesMatch_translate valid.1 offset,
    isOrthogonal_translate valid.2.1 offset,
    isPlanar_translate valid.2.2 offset⟩

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT
end LeanTrominoes
