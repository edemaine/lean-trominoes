import LeanTrominoes.OrthogonalPolylineStrictSeparation
import LeanTrominoes.EmbeddedCNFIncidenceDrawingMapPoints
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Closed bounding boxes for finite routes

This file packages the coordinate argument used whenever two finite
polylines occupy disjoint axis-aligned boxes.  Bounding every listed point
also bounds the endpoints of every polyline segment.  Strict separation of
the two boxes then rules out segment-interior intersections, point-in-
interior contacts, and shared listed points.
-/

namespace LeanTrominoes

/-- A lattice point lies in the closed axis-aligned rectangle with the
advertised lower and upper corners. -/
def InClosedGridRectangle
    (lower upper point : Cell) : Prop :=
  lower.1 ≤ point.1 ∧ point.1 ≤ upper.1 ∧
    lower.2 ≤ point.2 ∧ point.2 ≤ upper.2

instance (lower upper point : Cell) :
    Decidable (InClosedGridRectangle lower upper point) := by
  unfold InClosedGridRectangle
  infer_instance

/-- Two closed rectangles are separated by a strict gap in at least one
coordinate. -/
def ClosedGridRectanglesSeparated
    (firstLower firstUpper secondLower secondUpper : Cell) : Prop :=
  firstUpper.1 < secondLower.1 ∨
    secondUpper.1 < firstLower.1 ∨
      firstUpper.2 < secondLower.2 ∨
        secondUpper.2 < firstLower.2

instance (firstLower firstUpper secondLower secondUpper : Cell) :
    Decidable
      (ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) := by
  unfold ClosedGridRectanglesSeparated
  infer_instance

/-- Rectangle separation is symmetric. -/
theorem ClosedGridRectanglesSeparated.symm
    {firstLower firstUpper secondLower secondUpper : Cell}
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    ClosedGridRectanglesSeparated
      secondLower secondUpper firstLower firstUpper := by
  rcases separated with forwardX | backwardX | forwardY | backwardY
  · exact Or.inr (Or.inl forwardX)
  · exact Or.inl backwardX
  · exact Or.inr (Or.inr (Or.inr forwardY))
  · exact Or.inr (Or.inr (Or.inl backwardY))

/-- Points in separated closed rectangles are distinct. -/
theorem ne_of_inClosedGridRectangles_of_separated
    {firstLower firstUpper secondLower secondUpper
      firstPoint secondPoint : Cell}
    (firstBounded :
      InClosedGridRectangle firstLower firstUpper firstPoint)
    (secondBounded :
      InClosedGridRectangle secondLower secondUpper secondPoint)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    firstPoint ≠ secondPoint := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  rcases firstPoint with ⟨firstX, firstY⟩
  rcases secondPoint with ⟨secondX, secondY⟩
  simp only [InClosedGridRectangle] at firstBounded secondBounded
  simp only [ClosedGridRectanglesSeparated] at separated
  intro equal
  simp only [Prod.mk.injEq] at equal
  rcases separated with separated | separated |
      separated | separated <;> omega

/-- A point in one closed rectangle cannot lie in the relative interior of
an axis-aligned segment whose endpoints lie in a separated rectangle. -/
theorem not_interiorContains_of_inClosedGridRectangles_of_separated
    {pointLower pointUpper segmentLower segmentUpper point : Cell}
    {segment : GridSegment}
    (pointBounded :
      InClosedGridRectangle pointLower pointUpper point)
    (startBounded :
      InClosedGridRectangle segmentLower segmentUpper segment.start)
    (finishBounded :
      InClosedGridRectangle segmentLower segmentUpper segment.finish)
    (separated :
      ClosedGridRectanglesSeparated
        pointLower pointUpper segmentLower segmentUpper) :
    ¬segment.InteriorContains point := by
  rcases pointLower with ⟨pointLowerX, pointLowerY⟩
  rcases pointUpper with ⟨pointUpperX, pointUpperY⟩
  rcases segmentLower with ⟨segmentLowerX, segmentLowerY⟩
  rcases segmentUpper with ⟨segmentUpperX, segmentUpperY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [InClosedGridRectangle]
    at pointBounded startBounded finishBounded
  simp only [ClosedGridRectanglesSeparated] at separated
  simp only [GridSegment.InteriorContains,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.StrictlyBetween]
  rcases separated with separated | separated |
      separated | separated <;> omega

/-- Axis-aligned segment interiors whose endpoint boxes are separated do
not meet in the continuous plane. -/
theorem not_interiorsMeet_of_inClosedGridRectangles_of_separated
    {firstLower firstUpper secondLower secondUpper : Cell}
    {first second : GridSegment}
    (firstStart :
      InClosedGridRectangle firstLower firstUpper first.start)
    (firstFinish :
      InClosedGridRectangle firstLower firstUpper first.finish)
    (secondStart :
      InClosedGridRectangle secondLower secondUpper second.start)
    (secondFinish :
      InClosedGridRectangle secondLower secondUpper second.finish)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    ¬GridSegment.InteriorsMeet first second := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  simp only [InClosedGridRectangle]
    at firstStart firstFinish secondStart secondFinish
  simp only [ClosedGridRectanglesSeparated] at separated
  simp only [GridSegment.InteriorsMeet,
    GridSegment.IsHorizontal, GridSegment.IsVertical,
    GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween]
  rcases separated with separated | separated |
      separated | separated <;>
    simp_all [min_def, max_def] <;>
    omega

/-- Pointwise containment in separated closed rectangles gives complete
contact-free continuous separation of two finite routes. -/
theorem routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
    {firstLower firstUpper secondLower secondUpper : Cell}
    {first second : List Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle firstLower firstUpper point)
    (secondBounded :
      ∀ point ∈ second,
        InClosedGridRectangle secondLower secondUpper point)
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  unfold
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondMember
    exact
      not_interiorsMeet_of_inClosedGridRectangles_of_separated
        (firstBounded _ firstEndpoints.1)
        (firstBounded _ firstEndpoints.2)
        (secondBounded _ secondEndpoints.1)
        (secondBounded _ secondEndpoints.2)
        separated
  · intro firstPoint firstPointMember
      secondSegment secondSegmentMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember
    exact
      not_interiorContains_of_inClosedGridRectangles_of_separated
        (firstBounded _ firstPointMember)
        (secondBounded _ secondEndpoints.1)
        (secondBounded _ secondEndpoints.2)
        separated
  · intro secondPoint secondPointMember
      firstSegment firstSegmentMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstSegmentMember
    exact
      not_interiorContains_of_inClosedGridRectangles_of_separated
        (secondBounded _ secondPointMember)
        (firstBounded _ firstEndpoints.1)
        (firstBounded _ firstEndpoints.2)
        separated.symm
  · intro firstPoint firstPointMember
      secondPoint secondPointMember
    exact
      ne_of_inClosedGridRectangles_of_separated
        (firstBounded _ firstPointMember)
        (secondBounded _ secondPointMember)
        separated

namespace PlanarThreeSAT
namespace EmbeddedCNFIncidenceDrawing

/-- Every listed point of every genuine route in a finite incidence drawing
satisfies a common geometric predicate. -/
def RoutePointsSatisfy
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (predicate : Cell → Prop) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    ∀ point ∈ drawing.routeAt (drawing.incidenceAt incidenceIndex),
      predicate point

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (predicate : Cell → Prop) [DecidablePred predicate] :
    Decidable (drawing.RoutePointsSatisfy predicate) := by
  unfold RoutePointsSatisfy incidenceAt incidences routeAt
  infer_instance

/-- Whenever a listed route point equals one designated contact point, that
occurrence is one of the route's two advertised endpoints. -/
def RouteContactsAtEndpoint
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (contact : Cell) : Prop :=
  ∀ incidenceIndex : Fin drawing.incidences.length,
    ∀ point ∈ drawing.routeAt (drawing.incidenceAt incidenceIndex),
      point = contact →
        RoutePointIsEndpoint
          (drawing.routeAt (drawing.incidenceAt incidenceIndex)) point

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (contact : Cell) :
    Decidable (drawing.RouteContactsAtEndpoint contact) := by
  unfold RouteContactsAtEndpoint incidenceAt incidences routeAt
  infer_instance

/-- Finite route bounds can be used through clause- and literal-membership
witnesses without manually constructing a finite incidence index. -/
theorem RoutePointsSatisfy.of_members
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {predicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy predicate)
    {clause : EmbeddedClause Variable} {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool} {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈ drawing.routes clauseIndex literalIndex) :
    predicate point := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences := by
    exact (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have pointBounded :=
    bounded incidenceIndex point
  apply pointBounded
  change
    point ∈
      drawing.routes
        (drawing.incidenceAt incidenceIndex).clauseIndex
        (drawing.incidenceAt incidenceIndex).literalIndex
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  rw [incidenceAtEqual]
  exact pointMember

/-- A pointwise implication weakens a common route-point predicate. -/
theorem RoutePointsSatisfy.mono
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {sourcePredicate targetPredicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy sourcePredicate)
    (implies :
      ∀ point, sourcePredicate point → targetPredicate point) :
    drawing.RoutePointsSatisfy targetPredicate := by
  intro incidenceIndex point pointMember
  exact implies point
    (bounded incidenceIndex point pointMember)

/-- A drawing-level endpoint-contact certificate can be selected through
clause- and literal-membership witnesses. -/
theorem RouteContactsAtEndpoint.of_members
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {contact : Cell}
    (contacts : drawing.RouteContactsAtEndpoint contact)
    {clause : EmbeddedClause Variable} {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ drawing.formula.zipIdx)
    {literal : Variable × Bool} {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈ drawing.routes clauseIndex literalIndex)
    (pointEqual : point = contact) :
    RoutePointIsEndpoint
      (drawing.routes clauseIndex literalIndex) point := by
  let incidence : EmbeddedCNFIncidence Variable :=
    ⟨clause, clauseIndex, literal, literalIndex⟩
  have incidenceMember :
      incidence ∈ drawing.incidences := by
    exact (mem_embeddedCNFIncidences_iff
      drawing.formula incidence).mpr
        ⟨clauseMember, literalMember⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceEqual⟩
  have endpoint :=
    contacts incidenceIndex point
  change
    point ∈
      drawing.routes
        (drawing.incidenceAt incidenceIndex).clauseIndex
        (drawing.incidenceAt incidenceIndex).literalIndex →
      point = contact →
        RoutePointIsEndpoint
          (drawing.routes
            (drawing.incidenceAt incidenceIndex).clauseIndex
            (drawing.incidenceAt incidenceIndex).literalIndex)
          point
    at endpoint
  have incidenceAtEqual :
      drawing.incidenceAt incidenceIndex = incidence :=
    incidenceEqual
  rw [incidenceAtEqual] at endpoint
  exact endpoint pointMember pointEqual

/-- Logical variable renaming leaves all route-point bounds unchanged. -/
theorem RoutePointsSatisfy.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    {predicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy predicate)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename variableMap targetPosition).RoutePointsSatisfy
      predicate := by
  intro renamedIndex point pointMember
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence] at pointMember
  exact bounded originalIndex point pointMember

/-- Logical variable renaming leaves endpoint-only contact certificates
unchanged. -/
theorem RouteContactsAtEndpoint.rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    {contact : Cell}
    (contacts : drawing.RouteContactsAtEndpoint contact)
    (variableMap : Source → Target)
    (targetPosition : Target → Cell) :
    (drawing.rename
      variableMap targetPosition).RouteContactsAtEndpoint contact := by
  intro renamedIndex point pointMember pointEqual
  let originalIndex : Fin drawing.incidences.length :=
    ⟨renamedIndex.val, by
      exact renamedIndex.isLt.trans_eq
        (rename_incidences_length
          drawing variableMap targetPosition)⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  rw [incidenceEqual, routeAt_rename_incidence]
    at pointMember ⊢
  exact
    contacts originalIndex point pointMember pointEqual

/-- Conversely, a bound proved after logical renaming already bounds the
unchanged route family of the source drawing. -/
theorem RoutePointsSatisfy.of_rename
    {Source Target : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Source}
    {predicate : Cell → Prop}
    (variableMap : Source → Target)
    (targetPosition : Target → Cell)
    (bounded :
      (drawing.rename variableMap targetPosition).RoutePointsSatisfy
        predicate) :
    drawing.RoutePointsSatisfy predicate := by
  intro sourceIndex point pointMember
  let renamedIndex :
      Fin (drawing.rename
        variableMap targetPosition).incidences.length :=
    ⟨sourceIndex.val, by
      simpa using sourceIndex.isLt⟩
  have incidenceEqual :=
    incidenceAt_rename
      drawing variableMap targetPosition renamedIndex
  have renamedBounded :=
    bounded renamedIndex point
  rw [incidenceEqual, routeAt_rename_incidence]
    at renamedBounded
  exact renamedBounded pointMember

/-- Mapping every drawing point transports route-point bounds through any
predicate respected by the point map. -/
theorem RoutePointsSatisfy.mapPoints
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {sourcePredicate targetPredicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy sourcePredicate)
    (transform : Cell → Cell)
    (mapsPredicate :
      ∀ point, sourcePredicate point →
        targetPredicate (transform point)) :
    (drawing.mapPoints transform).RoutePointsSatisfy
      targetPredicate := by
  intro mappedIndex mappedPoint mappedPointMember
  let originalIndex : Fin drawing.incidences.length :=
    ⟨mappedIndex.val, by
      exact mappedIndex.isLt.trans_eq
        (mapPoints_incidences_length drawing transform)⟩
  have incidenceEqual :=
    incidenceAt_mapPoints drawing transform mappedIndex
  rw [incidenceEqual, routeAt_mapPoints_incidence]
    at mappedPointMember
  rcases List.mem_map.mp mappedPointMember with
    ⟨point, pointMember, pointEqual⟩
  subst mappedPoint
  exact mapsPredicate point
    (bounded originalIndex point pointMember)

/-- Mapping a route maps each advertised endpoint to an advertised endpoint
of the image route. -/
theorem RoutePointIsEndpoint.map
    {route : List Cell} {point : Cell}
    (endpoint : RoutePointIsEndpoint route point)
    (transform : Cell → Cell) :
    RoutePointIsEndpoint
      (route.map transform) (transform point) := by
  rcases endpoint with first | last
  · left
    simpa only [List.head?_map, Option.map_some] using
      congrArg (Option.map transform) first
  · right
    simpa only [List.getLast?_map, Option.map_some] using
      congrArg (Option.map transform) last

/-- An injective point map transports endpoint-only contact to the image
of the designated contact point. -/
theorem RouteContactsAtEndpoint.mapPoints
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {contact : Cell}
    (contacts : drawing.RouteContactsAtEndpoint contact)
    (transform : Cell → Cell)
    (injective : Function.Injective transform) :
    (drawing.mapPoints transform).RouteContactsAtEndpoint
      (transform contact) := by
  intro mappedIndex mappedPoint mappedPointMember contactEqual
  let originalIndex : Fin drawing.incidences.length :=
    ⟨mappedIndex.val, by
      exact mappedIndex.isLt.trans_eq
        (mapPoints_incidences_length drawing transform)⟩
  have incidenceEqual :=
    incidenceAt_mapPoints drawing transform mappedIndex
  rw [incidenceEqual, routeAt_mapPoints_incidence]
    at mappedPointMember ⊢
  rcases List.mem_map.mp mappedPointMember with
    ⟨point, pointMember, pointEqual⟩
  have sourceEqual : point = contact :=
    injective (pointEqual.trans contactEqual)
  have mappedEndpoint :=
    (contacts originalIndex point
      pointMember sourceEqual).map transform
  simpa [originalIndex, pointEqual] using mappedEndpoint

/-- Translation transports route-point bounds through any predicate that is
stable under adding the same offset. -/
theorem RoutePointsSatisfy.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {sourcePredicate targetPredicate : Cell → Prop}
    (bounded : drawing.RoutePointsSatisfy sourcePredicate)
    (offset : Cell)
    (mapsPredicate :
      ∀ point, sourcePredicate point →
        targetPredicate (Cell.add offset point)) :
    (drawing.translate offset).RoutePointsSatisfy targetPredicate := by
  intro translatedIndex translatedPoint translatedPointMember
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
    at translatedPointMember
  rcases List.mem_map.mp translatedPointMember with
    ⟨point, pointMember, pointEqual⟩
  subst translatedPoint
  exact mapsPredicate point
    (bounded originalIndex point pointMember)

/-- Translation transports endpoint-only contact to the translated contact
point. -/
theorem RouteContactsAtEndpoint.translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    {contact : Cell}
    (contacts : drawing.RouteContactsAtEndpoint contact)
    (offset : Cell) :
    (drawing.translate offset).RouteContactsAtEndpoint
      (Cell.add offset contact) := by
  intro translatedIndex translatedPoint
    translatedPointMember contactEqual
  let originalIndex : Fin drawing.incidences.length :=
    ⟨translatedIndex.val, by
      exact translatedIndex.isLt.trans_eq
        (translate_incidences_length drawing offset)⟩
  have incidenceEqual :=
    incidenceAt_translate drawing offset translatedIndex
  rw [incidenceEqual, routeAt_translate_incidence]
    at translatedPointMember ⊢
  rcases List.mem_map.mp translatedPointMember with
    ⟨point, pointMember, pointEqual⟩
  have sourceEqual : point = contact :=
    cell_add_left_injective offset
      (pointEqual.trans contactEqual)
  have translatedEndpoint :=
    (contacts originalIndex point
      pointMember sourceEqual).map (Cell.add offset)
  simpa [originalIndex, pointEqual] using translatedEndpoint

/-- A direct straight-line incidence drawing is bounded whenever all of its
clause positions and occurring variable positions are bounded. -/
theorem straightIncidenceDrawing_routePointsSatisfy
    {Variable : Type*}
    (formula : List (EmbeddedClause Variable))
    (variablePosition : Variable → Cell)
    (predicate : Cell → Prop)
    (clausesBounded :
      ∀ clause ∈ formula, predicate clause.position)
    (variablesBounded :
      ∀ clause ∈ formula,
        ∀ literal ∈ clause.literals,
          predicate (variablePosition literal.1)) :
    (straightIncidenceDrawing
      formula variablePosition).RoutePointsSatisfy predicate := by
  intro incidenceIndex point pointMember
  let incidence :=
    (straightIncidenceDrawing
      formula variablePosition).incidenceAt incidenceIndex
  have incidenceMember :
      incidence ∈
        (straightIncidenceDrawing
          formula variablePosition).incidences :=
    List.get_mem _ incidenceIndex
  change incidence ∈ embeddedCNFIncidences formula
    at incidenceMember
  have indexedMembers :=
    (mem_embeddedCNFIncidences_iff formula incidence).mp
      incidenceMember
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp indexedMembers.1
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp indexedMembers.2
  change
    point ∈
      straightIncidenceRoutes formula variablePosition
        incidence.clauseIndex incidence.literalIndex at pointMember
  simp [straightIncidenceRoutes, clauseLookup,
    literalLookup, straightIncidenceRoute] at pointMember
  rcases pointMember with pointEqual | pointEqual
  · subst point
    exact clausesBounded incidence.clause
      (List.fst_mem_of_mem_zipIdx indexedMembers.1)
  · subst point
    exact variablesBounded incidence.clause
      (List.fst_mem_of_mem_zipIdx indexedMembers.1)
      incidence.literal
      (List.fst_mem_of_mem_zipIdx indexedMembers.2)

/-- Every route point lies in one closed rectangle. -/
def RoutePointsInClosedRectangle
    {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (lower upper : Cell) : Prop :=
  drawing.RoutePointsSatisfy
    (InClosedGridRectangle lower upper)

instance {Variable : Type*}
    (drawing : EmbeddedCNFIncidenceDrawing Variable)
    (lower upper : Cell) :
    Decidable (drawing.RoutePointsInClosedRectangle lower upper) := by
  unfold RoutePointsInClosedRectangle
  infer_instance

end EmbeddedCNFIncidenceDrawing
end PlanarThreeSAT

end LeanTrominoes
