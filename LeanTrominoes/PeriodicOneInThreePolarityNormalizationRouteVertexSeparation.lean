import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteVertexBounds
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.PeriodicGridDrawingVertexCoverage

/-!
# Separation of polarity-normalization subdivision vertices

The two new vertices reserved on an incompatible incidence lie strictly in
the first segment of its threefold-scaled source route.  This characterization
reduces all new-vertex separation obligations to the source presentation's
integer and continuous planarity certificates.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Indexed lookup in a generated unit segment is its defining cardinal
step whenever the index is in range. -/
theorem unitSegmentPoints_getD_of_lt
    (first second : Cell)
    (pointIndex : Nat)
    (pointIndexLt :
      pointIndex < AxisDirection.segmentLength first second + 1) :
    (AxisDirection.unitSegmentPoints first second).getD
        pointIndex (0, 0) =
      Cell.add first
        (Cell.scale (pointIndex : Int)
          (AxisDirection.between first second).step) := by
  rw [List.getD_eq_getElem _ _ (by simpa using pointIndexLt)]
  simp [AxisDirection.unitSegmentPoints]

/-- The points at indices one and two of the unit subdivision of a
threefold-scaled first segment lie in that scaled segment's relative
interior. -/
theorem unitSubdivide_scale_three_getD_interior
    (first second : Cell)
    (rest : List Cell)
    (aligned : (GridSegment.mk first second).IsAxisAligned)
    (pointIndex : Nat)
    (pointIndexCases : pointIndex = 1 ∨ pointIndex = 2) :
    (GridSegment.mk
      (Cell.scale refinementFactor first)
      (Cell.scale refinementFactor second)).InteriorContains
        ((AxisDirection.unitSubdividePolyline
          (scalePolyline refinementFactor (first :: second :: rest)))
            |>.getD pointIndex (0, 0)) := by
  have sourceLengthPositive :=
    AxisDirection.segmentLength_positive_of_axisAligned aligned
  have scaledLength :
      AxisDirection.segmentLength
          (Cell.scale refinementFactor first)
          (Cell.scale refinementFactor second) =
        refinementFactor * AxisDirection.segmentLength first second :=
    segmentLength_scale_three first second
  have pointIndexLt :
      pointIndex <
        AxisDirection.segmentLength
            (Cell.scale refinementFactor first)
            (Cell.scale refinementFactor second) + 1 := by
    rw [scaledLength]
    rcases pointIndexCases with rfl | rfl <;>
      simp [refinementFactor] <;> omega
  have routePointEq :
      (AxisDirection.unitSubdividePolyline
          (scalePolyline refinementFactor (first :: second :: rest))).getD
            pointIndex (0, 0) =
        Cell.add (Cell.scale refinementFactor first)
          (Cell.scale (pointIndex : Int)
            (AxisDirection.between
              (Cell.scale refinementFactor first)
              (Cell.scale refinementFactor second)).step) := by
    rw [scalePolyline_cons, scalePolyline_cons,
      AxisDirection.unitSubdividePolyline, joinAtEndpoint,
      List.getD_append _ _ _ _]
    · exact unitSegmentPoints_getD_of_lt _ _ _ pointIndexLt
    · simpa using pointIndexLt
  rw [routePointEq]
  rcases pointIndexCases with rfl | rfl
  · rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical] at aligned
    rcases aligned with
        ⟨horizontal, nondegenerate⟩ |
        ⟨vertical, nondegenerate⟩
    · subst secondY
      by_cases forward : firstX < secondX
      · simp [refinementFactor, AxisDirection.between,
          forward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
      · have backward : secondX < firstX := by omega
        simp [refinementFactor, AxisDirection.between,
          forward, backward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
    · subst secondX
      by_cases forward : firstY < secondY
      · have unequal : firstY ≠ secondY := by omega
        simp [refinementFactor, AxisDirection.between,
          unequal, forward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
      · have backward : secondY < firstY := by omega
        have unequal : firstY ≠ secondY := by omega
        simp [refinementFactor, AxisDirection.between,
          unequal, forward, backward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
  · rcases first with ⟨firstX, firstY⟩
    rcases second with ⟨secondX, secondY⟩
    simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical] at aligned
    rcases aligned with
        ⟨horizontal, nondegenerate⟩ |
        ⟨vertical, nondegenerate⟩
    · subst secondY
      by_cases forward : firstX < secondX
      · simp [refinementFactor, AxisDirection.between,
          forward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
      · have backward : secondX < firstX := by omega
        simp [refinementFactor, AxisDirection.between,
          forward, backward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
    · subst secondX
      by_cases forward : firstY < secondY
      · have unequal : firstY ≠ secondY := by omega
        simp [refinementFactor, AxisDirection.between,
          unequal, forward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega
      · have backward : secondY < firstY := by omega
        have unequal : firstY ≠ secondY := by omega
        simp [refinementFactor, AxisDirection.between,
          unequal, forward, backward, AxisDirection.step, Cell.add, Cell.scale,
          GridSegment.InteriorContains, GridSegment.IsHorizontal,
          GridSegment.IsVertical, GridSegment.StrictlyBetween]
        omega

/-- The continuously planar source presentation after anchor normalization
and threefold scaling. -/
def scaledSourcePresentation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement) :
    PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
      (refinedSource source sourcePlacement)
      (refinedPlacement sourcePlacement) :=
  (presentation.anchorNormalize).scale refinementFactor_positive

/-- The scaled source presentation uses the unsubdivided threefold-scaled
source routes. -/
@[simp]
theorem scaledSourcePresentation_routes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    (clauseIndex literalIndex : Nat) :
    (scaledSourcePresentation presentation).routes
        clauseIndex literalIndex =
      scalePolyline refinementFactor
        (presentation.routes clauseIndex literalIndex) := by
  rfl

/-- Each reserved point is strictly internal to the first segment of its
threefold-scaled source route. -/
theorem routePoint_interior_first_scaled_segment
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (pointIndex : Nat)
    (pointIndexCases : pointIndex = 1 ∨ pointIndex = 2) :
    ∃ first second rest,
      presentation.routes sourceClauseIndex sourceLiteralIndex =
          first :: second :: rest ∧
      (GridSegment.mk first second).IsAxisAligned ∧
      (GridSegment.mk
        (Cell.scale refinementFactor first)
        (Cell.scale refinementFactor second)).InteriorContains
          (routePoint presentation.routes
            ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral)
            pointIndex) := by
  have routeLength := sourceRoute_length_ge_two_of_refined_members
    presentation sourceClauseMember sourceLiteralMember
  have routeOrthogonal := sourceRoute_orthogonal_of_refined_members
    presentation sourceClauseMember sourceLiteralMember
  generalize routeEq :
      presentation.routes sourceClauseIndex sourceLiteralIndex = route
      at routeLength routeOrthogonal ⊢
  cases route with
  | nil => simp at routeLength
  | cons first rest =>
      cases rest with
      | nil => simp at routeLength
      | cons second rest =>
          have aligned :
              (GridSegment.mk first second).IsAxisAligned :=
            (List.isChain_cons_cons.mp routeOrthogonal).1
          refine ⟨first, second, rest, ?_, aligned, ?_⟩
          · rfl
          · simpa [routePoint, refinedRoute, routeEq] using
              unitSubdivide_scale_three_getD_interior
                first second rest aligned pointIndex pointIndexCases

/-- A reserved point comes with the exact indexed first-segment occurrence
of the scaled source drawing whose interior contains it. -/
theorem exists_indexedSegment_of_routePoint
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (pointIndex : Nat)
    (pointIndexCases : pointIndex = 1 ∨ pointIndex = 2) :
    ∃ incidenceIndex first second rest indexed,
      (CNFIncidence.mk sourceClauseIndex sourceClause.literals
          sourceLiteralIndex sourceLiteral, incidenceIndex) ∈
        (PeriodicCNF.incidencesWithMetadata
          (refinedSource source sourcePlacement).erase).zipIdx ∧
      presentation.routes sourceClauseIndex sourceLiteralIndex =
        first :: second :: rest ∧
      indexed.routeIndex = incidenceIndex ∧
      indexed ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes).indexedSegments ∧
      indexed.segment =
        GridSegment.mk
          (Cell.scale refinementFactor first)
          (Cell.scale refinementFactor second) ∧
      indexed.segment.InteriorContains
        (routePoint presentation.routes
          ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral)
          pointIndex) := by
  rcases PositionedPeriodicCNF.exists_taggedIncidence_of_members
      (refinedSource source sourcePlacement)
      sourceClauseMember sourceLiteralMember with
    ⟨incidenceIndex, taggedMember⟩
  rcases routePoint_interior_first_scaled_segment
      presentation sourceClauseMember sourceLiteralMember
      pointIndex pointIndexCases with
    ⟨first, second, rest, routeEq, _aligned, interior⟩
  have routeTaggedMember :
      (scalePolyline refinementFactor
          (presentation.routes sourceClauseIndex sourceLiteralIndex),
        incidenceIndex) ∈
      ((PositionedPeriodicCNF.incidenceDrawing
        (refinedSource source sourcePlacement)
        (refinedPlacement sourcePlacement)
        (scaledSourcePresentation presentation).routes).edgeRoutes).zipIdx := by
    change
      (scalePolyline refinementFactor
          (presentation.routes sourceClauseIndex sourceLiteralIndex),
        incidenceIndex) ∈
        (PositionedPeriodicCNF.incidenceEdgeRoutes
          (refinedSource source sourcePlacement)
          (scaledSourcePresentation presentation).routes).zipIdx
    rw [PositionedPeriodicCNF.incidenceEdgeRoutes_eq_metadata_map,
      List.zipIdx_map]
    apply List.mem_map.mpr
    refine ⟨(CNFIncidence.mk sourceClauseIndex sourceClause.literals
        sourceLiteralIndex sourceLiteral, incidenceIndex),
      taggedMember, ?_⟩
    simp [scaledSourcePresentation_routes]
  let segmentIndex :
      Fin (gridPolylineSegments
        (scalePolyline refinementFactor
          (presentation.routes sourceClauseIndex sourceLiteralIndex))).length :=
    ⟨0, by rw [routeEq]; simp [scalePolyline, gridPolylineSegments]⟩
  let indexed : IndexedGridSegment :=
    ⟨incidenceIndex, segmentIndex,
      (gridPolylineSegments
        (scalePolyline refinementFactor
          (presentation.routes sourceClauseIndex sourceLiteralIndex))).get
            segmentIndex⟩
  have indexedMember :
      indexed ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes).indexedSegments :=
    PeriodicGridDrawing.indexedSegment_mem_of_route_mem
      routeTaggedMember segmentIndex
  have segmentEq :
      indexed.segment =
        GridSegment.mk
          (Cell.scale refinementFactor first)
          (Cell.scale refinementFactor second) := by
    simp [indexed, segmentIndex, routeEq, scalePolyline,
      gridPolylineSegments]
  refine ⟨incidenceIndex, first, second, rest, indexed,
    taggedMember, routeEq, rfl, indexedMember, segmentEq, ?_⟩
  rwa [segmentEq]

/-- No retained source vertex coincides with either reserved subdivision
point of any genuine source incidence. -/
theorem sourceVertex_ne_routePoint
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (pointIndex : Nat)
    (pointIndexCases : pointIndex = 1 ∨ pointIndex = 2)
    (vertexPosition : Cell)
    (vertexPositionMember :
      vertexPosition ∈
        (PositionedPeriodicCNF.incidenceDrawing
          (refinedSource source sourcePlacement)
          (refinedPlacement sourcePlacement)
          (scaledSourcePresentation presentation).routes).vertexPositions) :
    vertexPosition ≠
      routePoint presentation.routes
        ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral)
        pointIndex := by
  rcases exists_indexedSegment_of_routePoint
      presentation sourceClauseMember sourceLiteralMember
      pointIndex pointIndexCases with
    ⟨_incidenceIndex, _first, _second, _rest, indexed,
      _taggedMember, _routeEq, _routeIndexEq,
      indexedMember, _segmentEq, interior⟩
  intro positionEq
  have avoids :=
    (scaledSourcePresentation presentation).planar.2
      vertexPosition vertexPositionMember indexed indexedMember
      (0, 0) (0, 0)
  apply avoids
  simpa [PeriodicGridDrawing.periodTranslation,
    GridSegment.translate, Cell.scale, Cell.add, positionEq] using interior

/-- The two reserved vertices on one refined incidence are distinct because
they are consecutive endpoints of a genuine unit step. -/
theorem routePoint_one_ne_two
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {sourceClause : PositionedPeriodicClause Variable}
    {sourceClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx) :
    routePoint presentation.routes
        ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 1 ≠
      routePoint presentation.routes
        ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 2 := by
  have routeLength := refinedRoute_length_ge_four_of_members
    presentation sourceClauseMember sourceLiteralMember
  have routeUnitSteps := refinedRoute_unitSteps_of_members
    presentation sourceClauseMember sourceLiteralMember
  have reverseUnitSteps := reverse_middle_unitSteps
    (refinedRoute presentation.routes
      sourceClauseIndex sourceLiteralIndex)
    routeLength routeUnitSteps
  have step :
      AxisDirection.IsUnitAxisStep
        (routePoint presentation.routes
          ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 2)
        (routePoint presentation.routes
          ((sourceClauseIndex, sourceLiteralIndex), sourceLiteral) 1) := by
    simpa [routePoint] using
      (List.isChain_cons_cons.mp reverseUnitSteps).1
  intro equal
  rcases step with ⟨direction, genuine, stepEq⟩
  rw [equal] at stepEq
  cases direction with
  | east =>
      have coordinate := congrArg Prod.fst stepEq
      simp [AxisDirection.step, Cell.add] at coordinate
  | north =>
      have coordinate := congrArg Prod.snd stepEq
      simp [AxisDirection.step, Cell.add] at coordinate
  | west =>
      have coordinate := congrArg Prod.fst stepEq
      simp [AxisDirection.step, Cell.add] at coordinate
  | south =>
      have coordinate := congrArg Prod.snd stepEq
      simp [AxisDirection.step, Cell.add] at coordinate
  | invalid => exact genuine rfl

/-- Reserved points belonging to different source occurrences are distinct,
because the corresponding scaled segment occurrences have disjoint relative
interiors. -/
theorem routePoint_ne_of_occurrence_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.ContinuousPlanarIncidencePresentation
        source sourcePlacement)
    {firstClause secondClause : PositionedPeriodicClause Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (refinedSource source sourcePlacement).clauses.zipIdx)
    {firstLiteral secondLiteral : PeriodicLiteral Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstPointIndex secondPointIndex : Nat)
    (firstPointIndexCases :
      firstPointIndex = 1 ∨ firstPointIndex = 2)
    (secondPointIndexCases :
      secondPointIndex = 1 ∨ secondPointIndex = 2)
    (occurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), firstLiteral) ≠
        ((secondClauseIndex, secondLiteralIndex), secondLiteral)) :
    routePoint presentation.routes
        ((firstClauseIndex, firstLiteralIndex), firstLiteral)
        firstPointIndex ≠
      routePoint presentation.routes
        ((secondClauseIndex, secondLiteralIndex), secondLiteral)
        secondPointIndex := by
  rcases exists_indexedSegment_of_routePoint
      presentation firstClauseMember firstLiteralMember
      firstPointIndex firstPointIndexCases with
    ⟨firstIncidenceIndex, _firstStart, _firstFinish, _firstRest,
      firstIndexed, firstTaggedMember, _firstRouteEq,
      firstRouteIndexEq, firstIndexedMember, _firstSegmentEq,
      firstInterior⟩
  rcases exists_indexedSegment_of_routePoint
      presentation secondClauseMember secondLiteralMember
      secondPointIndex secondPointIndexCases with
    ⟨secondIncidenceIndex, _secondStart, _secondFinish, _secondRest,
      secondIndexed, secondTaggedMember, _secondRouteEq,
      secondRouteIndexEq, secondIndexedMember, _secondSegmentEq,
      secondInterior⟩
  have occurrenceKeysDifferent :
      PeriodicGridDrawing.SegmentOccurrenceKey firstIndexed (0, 0) ≠
        PeriodicGridDrawing.SegmentOccurrenceKey secondIndexed (0, 0) := by
    intro keysEqual
    have routeIndexEq : firstIndexed.routeIndex = secondIndexed.routeIndex :=
      congrArg (fun key => key.1) keysEqual
    rw [firstRouteIndexEq, secondRouteIndexEq] at routeIndexEq
    have firstLookup :=
      (List.mem_zipIdx_iff_getElem?).mp firstTaggedMember
    have secondLookup :=
      (List.mem_zipIdx_iff_getElem?).mp secondTaggedMember
    rw [routeIndexEq, secondLookup] at firstLookup
    have incidenceEq :
        CNFIncidence.mk firstClauseIndex firstClause.literals
            firstLiteralIndex firstLiteral =
          CNFIncidence.mk secondClauseIndex secondClause.literals
            secondLiteralIndex secondLiteral :=
      Option.some.inj firstLookup.symm
    apply occurrencesDifferent
    exact congrArg
      (fun incidence : CNFIncidence Variable =>
        ((incidence.clauseIndex, incidence.literalIndex),
          incidence.literal)) incidenceEq
  have disjoint :=
    (scaledSourcePresentation presentation).continuouslyPlanar.noInteriorsMeet
      firstIndexedMember secondIndexedMember occurrenceKeysDifferent
  intro pointsEqual
  apply disjoint
  have secondAtFirst :
      secondIndexed.segment.InteriorContains
        (routePoint presentation.routes
          ((firstClauseIndex, firstLiteralIndex), firstLiteral)
          firstPointIndex) := by
    rw [pointsEqual]
    exact secondInterior
  have rawMeet :
      firstIndexed.segment.InteriorsMeet secondIndexed.segment :=
    GridSegment.interiorsMeet_of_interiorContains
      firstInterior secondAtFirst
  simpa [PeriodicGridDrawing.periodTranslation,
    GridSegment.translate, Cell.scale, Cell.add] using rawMeet

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
