import LeanTrominoes.PeriodicGridDrawingAffineUnitRefinement
import LeanTrominoes.PeriodicGridDrawingExpandedFiniteContinuousPlanarity
import LeanTrominoes.PeriodicGridDrawingEndpointContacts
import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicThreeDMIncidenceVertexCoverage

/-!
# Finite certificates for continuously planar periodic 3DM drawings

All unbounded geometric obligations used by the normalization compiler reduce
to finite checks when route endpoints lie in the open one-cell halo.  This
module combines those checks with finite compatibility and orthogonality
checks, and reconstructs the proof-carrying presentation consumed downstream.
-/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace FiniteDrawingCertificate

/-- Executable form of strict containment in the fundamental square. -/
def positionInFundamentalSquareCheck
    (drawing : PeriodicGridDrawing) (position : Cell) : Bool :=
  decide (0 < position.1) &&
    (decide (position.1 < drawing.gridSize) &&
      (decide (0 < position.2) &&
        decide (position.2 < drawing.gridSize)))

/-- Executable route-endpoint compatibility. -/
def routesMatchCheck (problem : PeriodicThreeDM)
    (drawing : PeriodicGridDrawing) : Bool :=
  problem.incidenceGraph.edges.zipIdx.all fun taggedEdge =>
    decide
      ((drawing.edgeRoute taggedEdge.2).head? =
          some (drawing.vertexPosition problem.incidenceGraph
            taggedEdge.1.source) ∧
        (drawing.edgeRoute taggedEdge.2).getLast? =
          some (Cell.add
            (drawing.vertexPosition problem.incidenceGraph
              taggedEdge.1.target)
            (drawing.periodTranslation taggedEdge.1.offset)))

/-- Finite compatibility conditions, apart from graph well-formedness (which
is a property of the 3DM problem rather than of a candidate drawing). -/
def compatibleCheck (problem : PeriodicThreeDM)
    (drawing : PeriodicGridDrawing) : Bool :=
  decide (drawing.vertexPositions.length =
      problem.incidenceGraph.vertices.length) &&
    (decide (drawing.edgeRoutes.length =
      problem.incidenceGraph.edges.length) &&
    (decide drawing.vertexPositions.Nodup &&
    ((drawing.vertexPositions.all fun position =>
      positionInFundamentalSquareCheck drawing position) &&
      routesMatchCheck problem drawing)))

theorem compatibleCheck_spec
    {problem : PeriodicThreeDM} {drawing : PeriodicGridDrawing}
    (problemWellFormed : problem.IsWellFormed)
    (checked : compatibleCheck problem drawing = true) :
    drawing.IsCompatible problem.incidenceGraph := by
  have graphWellFormed : problem.incidenceGraph.IsWellFormed :=
    problem.incidenceGraph_isWellFormed problemWellFormed
  simp only [compatibleCheck, positionInFundamentalSquareCheck,
    routesMatchCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at checked
  exact
    ⟨graphWellFormed, checked.1, checked.2.1, checked.2.2.1,
      (fun position member => by
        simpa [PeriodicGridDrawing.PositionInFundamentalSquare] using
          checked.2.2.2.1 position member),
      checked.2.2.2.2⟩

theorem compatibleCheck_complete
    {problem : PeriodicThreeDM} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible problem.incidenceGraph) :
    compatibleCheck problem drawing = true := by
  simp only [compatibleCheck, positionInFundamentalSquareCheck,
    routesMatchCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  exact
    ⟨compatible.2.1, compatible.2.2.1, compatible.2.2.2.1,
      (fun position member => by
        simpa [PeriodicGridDrawing.PositionInFundamentalSquare] using
          compatible.2.2.2.2.1 position member),
      compatible.2.2.2.2.2⟩

/-- Every listed segment is axis aligned. -/
def orthogonalCheck (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun indexed =>
    decide indexed.segment.IsAxisAligned

theorem orthogonalCheck_spec
    {drawing : PeriodicGridDrawing}
    (checked : orthogonalCheck drawing = true) :
    drawing.IsOrthogonal := by
  simpa [orthogonalCheck, PeriodicGridDrawing.IsOrthogonal] using checked

theorem orthogonalCheck_complete
    {drawing : PeriodicGridDrawing}
    (orthogonal : drawing.IsOrthogonal) :
    orthogonalCheck drawing = true := by
  simpa [orthogonalCheck, PeriodicGridDrawing.IsOrthogonal] using orthogonal

/-- Every listed segment endpoint lies in the open one-cell halo. -/
def endpointBoundsCheck (drawing : PeriodicGridDrawing) : Bool :=
  drawing.indexedSegments.all fun indexed =>
    (decide (-((drawing.gridSize : Nat) : Int) < indexed.segment.start.1) &&
      (decide (indexed.segment.start.1 < 2 * (drawing.gridSize : Nat)) &&
      (decide (-((drawing.gridSize : Nat) : Int) < indexed.segment.start.2) &&
        decide (indexed.segment.start.2 < 2 * (drawing.gridSize : Nat))))) &&
    (decide (-((drawing.gridSize : Nat) : Int) < indexed.segment.finish.1) &&
      (decide (indexed.segment.finish.1 < 2 * (drawing.gridSize : Nat)) &&
      (decide (-((drawing.gridSize : Nat) : Int) < indexed.segment.finish.2) &&
        decide (indexed.segment.finish.2 < 2 * (drawing.gridSize : Nat)))))

theorem endpointBoundsCheck_spec
    {drawing : PeriodicGridDrawing}
    (checked : endpointBoundsCheck drawing = true) :
    drawing.SegmentEndpointsInExpandedSquare := by
  intro indexed member
  have raw := checked
  simp only [endpointBoundsCheck, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at raw
  simpa [PeriodicGridDrawing.PositionInExpandedSquare] using
    raw indexed member

theorem endpointBoundsCheck_complete
    {drawing : PeriodicGridDrawing}
    (bounds : drawing.SegmentEndpointsInExpandedSquare) :
    endpointBoundsCheck drawing = true := by
  simp only [endpointBoundsCheck, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  intro indexed member
  simpa [PeriodicGridDrawing.PositionInExpandedSquare] using
    bounds indexed member

/-- Global route-interior avoidance makes the expanded finite route check
accept. -/
theorem expandedFiniteRoutesAvoidInteriors_complete
    {drawing : PeriodicGridDrawing}
    (avoids : drawing.RoutesAvoidInteriors) :
    drawing.expandedFiniteRoutesAvoidInteriors = true := by
  simp only [PeriodicGridDrawing.expandedFiniteRoutesAvoidInteriors,
    List.all_eq_true]
  intro first firstMember second secondMember relative _relativeMember
    point pointMember
  rw [decide_eq_true_eq]
  by_cases same :
      PeriodicGridDrawing.SegmentOccurrenceKey first relative =
        PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0)
  · exact Or.inl same
  · exact Or.inr (by
      simpa [PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale,
        GridSegment.translate] using
        avoids first firstMember second secondMember
          relative (0, 0) point same
          ((PeriodicGridDrawing.mem_segmentInteriorPoints_iff _ _).mp
            pointMember))

/-- Global vertex/route separation makes the nine-neighbor finite vertex
check accept. -/
theorem finiteVerticesAvoidRouteInteriors_complete
    {drawing : PeriodicGridDrawing}
    (avoids : drawing.VerticesAvoidRouteInteriors) :
    drawing.finiteVerticesAvoidRouteInteriors = true := by
  simp only [PeriodicGridDrawing.finiteVerticesAvoidRouteInteriors,
    List.all_eq_true]
  intro vertex vertexMember indexed indexedMember relative _relativeMember
  rw [decide_eq_true_eq]
  simpa [PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale] using
    avoids vertex vertexMember indexed indexedMember (0, 0) relative

/-- Global continuous segment-interior separation makes its expanded finite
check accept. -/
theorem expandedFiniteRoutesHaveDisjointInteriors_complete
    {drawing : PeriodicGridDrawing}
    (disjoint : drawing.RoutesHaveDisjointInteriors) :
    drawing.expandedFiniteRoutesHaveDisjointInteriors = true := by
  simp only [PeriodicGridDrawing.expandedFiniteRoutesHaveDisjointInteriors,
    List.all_eq_true]
  intro first firstMember second secondMember relative _relativeMember
  rw [decide_eq_true_eq]
  by_cases same :
      PeriodicGridDrawing.SegmentOccurrenceKey first relative =
        PeriodicGridDrawing.SegmentOccurrenceKey second (0, 0)
  · exact Or.inl same
  · exact Or.inr (by
      simpa [PeriodicGridDrawing.periodTranslation, Cell.add, Cell.scale,
        GridSegment.translate] using
        disjoint first firstMember second secondMember
          relative (0, 0) same)

/-- Global endpoint-only listed-point contacts make their expanded finite
check accept. -/
theorem expandedFiniteRoutePointsMeetOnlyAtEndpoints_complete
    {drawing : PeriodicGridDrawing}
    (contacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    drawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints = true := by
  simp only [PeriodicGridDrawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints,
    List.all_eq_true]
  intro first firstMember second secondMember relative _relativeMember
  rw [decide_eq_true_eq]
  by_cases same :
      PeriodicGridDrawing.RoutePointOccurrenceKey first relative =
        PeriodicGridDrawing.RoutePointOccurrenceKey second (0, 0)
  · exact Or.inl same
  · right
    by_cases unequal :
        Cell.add first.point (drawing.periodTranslation relative) ≠
          second.point
    · exact Or.inl unequal
    · exact Or.inr (contacts first firstMember second secondMember
        relative (0, 0) same (by
          simpa [PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale] using not_ne_iff.mp unequal))

/-- The complete Boolean certificate searched for by the computable drawing
selector. -/
def verifies (problem : PeriodicThreeDM)
    (drawing : PeriodicGridDrawing) : Bool :=
  compatibleCheck problem drawing &&
    (orthogonalCheck drawing &&
      (endpointBoundsCheck drawing &&
        (drawing.expandedFiniteRoutesAvoidInteriors &&
          (drawing.finiteVerticesAvoidRouteInteriors &&
            (drawing.expandedFiniteRoutesHaveDisjointInteriors &&
              drawing.expandedFiniteRoutePointsMeetOnlyAtEndpoints)))))

/-- Every globally certified halo-bounded drawing passes the combined finite
checker. -/
theorem verifies_complete
    {problem : PeriodicThreeDM} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible problem.incidenceGraph)
    (orthogonal : drawing.IsOrthogonal)
    (endpointBounds : drawing.SegmentEndpointsInExpandedSquare)
    (continuous : drawing.IsContinuouslyPlanar)
    (endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    verifies problem drawing = true := by
  simp only [verifies, Bool.and_eq_true]
  exact
    ⟨compatibleCheck_complete compatible,
      orthogonalCheck_complete orthogonal,
      endpointBoundsCheck_complete endpointBounds,
      expandedFiniteRoutesAvoidInteriors_complete continuous.1.1,
      finiteVerticesAvoidRouteInteriors_complete continuous.1.2,
      expandedFiniteRoutesHaveDisjointInteriors_complete continuous.2,
      expandedFiniteRoutePointsMeetOnlyAtEndpoints_complete endpointContacts⟩

/-- Proof-carrying output reconstructed from a successful finite check. -/
structure CertifiedPresentation (problem : PeriodicThreeDM) where
  presentation : problem.ContinuousPlanarPresentation
  endpointBounds :
    presentation.drawing.SegmentEndpointsInExpandedSquare
  routePointsInExpandedSquare :
    presentation.drawing.RoutePointsInExpandedSquare
  separated : presentation.drawing.LiftedRoutesAvoidEachOther
  routesSimple :
    ∀ route ∈ presentation.drawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route

/-- A successful finite certificate reconstructs all geometric properties
needed by the normalized-drawing compiler. -/
noncomputable def certifiedPresentationOfVerified
    {problem : PeriodicThreeDM} {drawing : PeriodicGridDrawing}
    (problemWellFormed : problem.IsWellFormed)
    (checked : verifies problem drawing = true) :
    CertifiedPresentation problem := by
  simp only [verifies, Bool.and_eq_true] at checked
  have compatible := compatibleCheck_spec problemWellFormed checked.1
  have orthogonal := orthogonalCheck_spec checked.2.1
  have endpointBounds := endpointBoundsCheck_spec checked.2.2.1
  have continuouslyPlanar : drawing.IsContinuouslyPlanar :=
    PeriodicGridDrawing.isContinuouslyPlanar_of_expandedFinite
      endpointBounds compatible.2.2.2.2.1
      checked.2.2.2.1 checked.2.2.2.2.1 checked.2.2.2.2.2.1
  have routeLengths :
      ∀ route ∈ drawing.edgeRoutes, 2 ≤ route.length := by
    intro route routeMember
    exact
      PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
        problem.incidenceGraph drawing compatible
        (problem.incidenceGraph_edgesAreLoopless) routeMember
  have routePointBounds : drawing.RoutePointsInExpandedSquare :=
    PeriodicGridDrawing.routePointsInExpandedSquare_of_segmentEndpoints
      endpointBounds routeLengths
  have endpointContacts : drawing.RoutePointsMeetOnlyAtEndpoints :=
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_of_expandedFinite
      routePointBounds checked.2.2.2.2.2.2
  have separated : drawing.LiftedRoutesAvoidEachOther :=
    PeriodicGridDrawing.liftedRoutesAvoidEachOther_of_isRibbonReady_of_isOrthogonal
      ⟨continuouslyPlanar, endpointContacts⟩ orthogonal routeLengths
  have routesSimple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route :=
    PeriodicGridDrawing.routesSimple_of_globalCertificates_of_compatible_of_loopless
      problem.incidenceGraph drawing compatible
      problem.incidenceGraph_edgesAreLoopless continuouslyPlanar
      endpointContacts orthogonal
  let presentation : problem.ContinuousPlanarPresentation :=
    { drawing := drawing
      problemWellFormed := problemWellFormed
      compatible := compatible
      orthogonal := orthogonal
      planar := continuouslyPlanar.1
      continuouslyPlanar := continuouslyPlanar }
  exact
    { presentation := presentation
      endpointBounds := endpointBounds
      routePointsInExpandedSquare := routePointBounds
      separated := separated
      routesSimple := routesSimple }

end FiniteDrawingCertificate
end PeriodicThreeDM
end LeanTrominoes
