import LeanTrominoes.PeriodicOrthocrossingPlanarCarrierSoundness
import LeanTrominoes.PeriodicOrthocrossingPlanarEndpoints

/-!
# Soundness along complete routed polylines

Straight-segment soundness composes through the bend equalities.  The main
result of this file says that any satisfying route core gives the same value
to the canonical first and last terminals of every listed neighboring
translated protoedge route.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A terminal built from a tagged segment of one route. -/
def taggedRouteSegmentTerminal
    (routeIndex : Nat) (translate : Cell)
    (taggedSegment : GridSegment × Nat)
    (endpoint : SegmentEnd) : SegmentTerminal :=
  ⟨⟨routeIndex, taggedSegment.2, taggedSegment.1⟩,
    translate, endpoint⟩

/-- If every straight segment and every bend in a polyline propagates its
value, then the first segment's start equals the last segment's finish.
The starting segment index is explicit so the induction hypothesis can
recurse on the tail polyline without renumbering it. -/
theorem routeTerminals_assignment_eq_aux
    (assignment : CarrierNode → Bool)
    (routeIndex : Nat) (translate : Cell) :
    ∀ (points : List Cell) (startIndex : Nat)
      (first : GridSegment × Nat)
      (rest : List (GridSegment × Nat)),
      (gridPolylineSegments points).zipIdx startIndex =
          first :: rest →
      (∀ taggedSegment ∈
          (gridPolylineSegments points).zipIdx startIndex,
        assignment
            (.terminal
              (taggedRouteSegmentTerminal routeIndex translate
                taggedSegment .start)) =
          assignment
            (.terminal
              (taggedRouteSegmentTerminal routeIndex translate
                taggedSegment .finish))) →
      (∀ routeBend ∈
          routeBendsAux routeIndex translate startIndex points,
        assignment (.terminal routeBend.incomingTerminal) =
          assignment (.terminal routeBend.outgoingTerminal)) →
      assignment
          (.terminal
            (taggedRouteSegmentTerminal routeIndex translate
              first .start)) =
        assignment
          (.terminal
            (taggedRouteSegmentTerminal routeIndex translate
              ((first :: rest).getLastD first) .finish)) := by
  intro points
  induction points using List.twoStepInduction with
  | nil =>
      intro startIndex first rest segmentsEq
      simp [gridPolylineSegments] at segmentsEq
  | singleton point =>
      intro startIndex first rest segmentsEq
      simp [gridPolylineSegments] at segmentsEq
  | cons_cons firstPoint secondPoint tail
      headInduction tailInduction =>
      intro startIndex first rest segmentsEq
        segmentLaws bendLaws
      cases tail with
      | nil =>
          simp only [gridPolylineSegments, List.zipIdx_cons,
            List.zipIdx_nil] at segmentsEq
          injection segmentsEq with firstEq restEq
          subst first
          subst rest
          simpa using
            segmentLaws
              (⟨⟨firstPoint, secondPoint⟩, startIndex⟩)
              (by simp [gridPolylineSegments])
      | cons thirdPoint tail =>
          simp only [gridPolylineSegments, List.zipIdx_cons]
            at segmentsEq
          injection segmentsEq with firstEq restEq
          subst first
          subst rest
          have firstSegment :=
            segmentLaws
              (⟨⟨firstPoint, secondPoint⟩, startIndex⟩)
              (by simp [gridPolylineSegments])
          let firstBend : RouteBend :=
            ⟨routeIndex, startIndex, translate,
              firstPoint, secondPoint, thirdPoint⟩
          have bendEq :
              assignment
                  (.terminal firstBend.incomingTerminal) =
                assignment
                  (.terminal firstBend.outgoingTerminal) :=
            bendLaws firstBend (by
              simp [routeBendsAux, firstBend])
          have tailSegments :
              (gridPolylineSegments
                (secondPoint :: thirdPoint :: tail)).zipIdx
                  (startIndex + 1) =
                (⟨secondPoint, thirdPoint⟩, startIndex + 1) ::
                  (gridPolylineSegments
                    (thirdPoint :: tail)).zipIdx
                      (startIndex + 2) := by
            simp [gridPolylineSegments, Nat.add_assoc]
          have tailSegmentLaws :
              ∀ taggedSegment ∈
                  (gridPolylineSegments
                    (secondPoint :: thirdPoint :: tail)).zipIdx
                      (startIndex + 1),
                assignment
                    (.terminal
                      (taggedRouteSegmentTerminal routeIndex translate
                        taggedSegment .start)) =
                  assignment
                    (.terminal
                      (taggedRouteSegmentTerminal routeIndex translate
                        taggedSegment .finish)) := by
            intro taggedSegment taggedSegmentMem
            apply segmentLaws taggedSegment
            change taggedSegment ∈
              (⟨⟨firstPoint, secondPoint⟩, startIndex⟩ ::
                (gridPolylineSegments
                  (secondPoint :: thirdPoint :: tail)).zipIdx
                    (startIndex + 1))
            exact List.mem_cons_of_mem _ taggedSegmentMem
          have tailBendLaws :
              ∀ routeBend ∈
                  routeBendsAux routeIndex translate (startIndex + 1)
                    (secondPoint :: thirdPoint :: tail),
                assignment (.terminal routeBend.incomingTerminal) =
                  assignment
                    (.terminal routeBend.outgoingTerminal) := by
            intro routeBend routeBendMem
            apply bendLaws routeBend
            simp only [routeBendsAux, List.mem_cons]
            exact Or.inr routeBendMem
          have tailEq :=
            tailInduction secondPoint (startIndex + 1)
              (⟨secondPoint, thirdPoint⟩, startIndex + 1)
              ((gridPolylineSegments
                (thirdPoint :: tail)).zipIdx (startIndex + 2))
              tailSegments tailSegmentLaws tailBendLaws
          have tailLastEq :
              (((⟨firstPoint, secondPoint⟩, startIndex) ::
                (⟨secondPoint, thirdPoint⟩, startIndex + 1) ::
                  (gridPolylineSegments
                    (thirdPoint :: tail)).zipIdx
                      (startIndex + 2)).getLastD
                        (⟨firstPoint, secondPoint⟩, startIndex)) =
                (((⟨secondPoint, thirdPoint⟩, startIndex + 1) ::
                  (gridPolylineSegments
                    (thirdPoint :: tail)).zipIdx
                      (startIndex + 2)).getLastD
                        (⟨secondPoint, thirdPoint⟩,
                          startIndex + 1)) := by
            calc
              _ =
                  ((gridPolylineSegments
                    (thirdPoint :: tail)).zipIdx
                      (startIndex + 2)).getLastD
                        (⟨secondPoint, thirdPoint⟩,
                          startIndex + 1) := by
                    rw [List.getLastD_cons,
                      List.getLastD_cons]
              _ = _ := by
                rw [List.getLastD_cons]
          change
            assignment
                (.terminal
                  (taggedRouteSegmentTerminal routeIndex translate
                    (⟨firstPoint, secondPoint⟩, startIndex)
                    .start)) =
              assignment
                (.terminal
                  (taggedRouteSegmentTerminal routeIndex translate
                    (((⟨firstPoint, secondPoint⟩, startIndex) ::
                      (⟨secondPoint, thirdPoint⟩, startIndex + 1) ::
                        (gridPolylineSegments
                          (thirdPoint :: tail)).zipIdx
                            (startIndex + 2)).getLastD
                              (⟨firstPoint, secondPoint⟩, startIndex))
                    .finish))
          rw [tailLastEq]
          exact firstSegment.trans (bendEq.trans (by
            simpa [firstBend, taggedRouteSegmentTerminal,
              RouteBend.incomingTerminal,
              RouteBend.outgoingTerminal,
              List.getLastD_cons] using tailEq))

/-- A tagged protoedge occurs at the same numeric index in the constructed
route list. -/
theorem constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (taggedEdgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2,
        taggedEdge.2) ∈
      (drawing graph).edgeRoutes.zipIdx := by
  apply (List.mem_zipIdx_iff_getElem?).mpr
  have lookup :=
    (List.mem_zipIdx_iff_getElem?).mp taggedEdgeMem
  simp [drawing, constructedEdgeRoutes,
    List.getElem?_map, lookup]

/-- A segment tagged inside a constructed protoedge route is one of the
completed drawing's indexed segments. -/
theorem constructedRouteSegment_mem_drawing_indexedSegments
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (taggedEdgeMem : taggedEdge ∈ graph.edges.zipIdx)
    {taggedSegment : GridSegment × Nat}
    (taggedSegmentMem :
      taggedSegment ∈
        (gridPolylineSegments
          (constructedEdgeRoute graph
            taggedEdge.1 taggedEdge.2)).zipIdx) :
    (⟨taggedEdge.2, taggedSegment.2, taggedSegment.1⟩ :
      IndexedGridSegment) ∈
        (drawing graph).indexedSegments := by
  apply mem_drawing_indexedSegments_iff.mpr
  have nestedRouteMem :
      (taggedEdge, taggedEdge.2) ∈
        graph.edges.zipIdx.zipIdx := by
    apply (List.mem_zipIdx_iff_getElem?).mpr
    have lookup :=
      (List.mem_zipIdx_iff_getElem?).mp taggedEdgeMem
    simp [List.getElem?_zipIdx, lookup]
  exact
    ⟨(taggedEdge, taggedEdge.2), nestedRouteMem,
      taggedSegment, taggedSegmentMem, rfl⟩

/-- The first and last terminals of one listed neighboring constructed route
have equal values under the three propagation-law families. -/
theorem constructedRouteTerminals_assignment_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (crossingLaws :
      ∀ crossing ∈ orientedCrossings graph,
        assignment
            (.inl (.boundary ⟨crossing, .left⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .right⟩)) ∧
          assignment
              (.inl (.boundary ⟨crossing, .top⟩)) =
            assignment
              (.inl (.boundary ⟨crossing, .bottom⟩)))
    (carrierLaws :
      ∀ link ∈ drawingCompleteCarrierLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second))
    (bendLaws :
      ∀ link ∈ drawingRouteBendLinks graph,
        assignment (.inl link.first) =
          assignment (.inl link.second))
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (taggedEdgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate)
    (default : GridSegment × Nat) :
    let segments :=
      (gridPolylineSegments
        (constructedEdgeRoute graph
          taggedEdge.1 taggedEdge.2)).zipIdx
    let first := segments.getD 0 default
    let last := segments.getLastD default
    assignment
        (.inl (.terminal
          (taggedRouteSegmentTerminal taggedEdge.2 translate
            first .start))) =
      assignment
        (.inl (.terminal
          (taggedRouteSegmentTerminal taggedEdge.2 translate
            last .finish))) := by
  let points :=
    constructedEdgeRoute graph taggedEdge.1 taggedEdge.2
  let segments :=
    (gridPolylineSegments points).zipIdx
  have routeLong : 2 ≤ points.length := by
    unfold points constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf taggedEdge.1.source))
        (portX graph (sourcePort taggedEdge.1 taggedEdge.2))
    omega
  have segmentsNonempty : segments ≠ [] := by
    intro segmentsEmpty
    have lengthZero := congrArg List.length segmentsEmpty
    simp only [segments, List.length_zipIdx,
      gridPolylineSegments_length, List.length_nil] at lengthZero
    omega
  have segmentLaws :
      ∀ taggedSegment ∈ segments,
        assignment
            (.inl (.terminal
              (taggedRouteSegmentTerminal taggedEdge.2 translate
                taggedSegment .start))) =
          assignment
            (.inl (.terminal
              (taggedRouteSegmentTerminal taggedEdge.2 translate
                taggedSegment .finish))) := by
    intro taggedSegment taggedSegmentMem
    exact segmentOccurrenceTerminals_assignment_eq
      graph assignment crossingLaws carrierLaws
      ⟨taggedEdge.2, taggedSegment.2, taggedSegment.1⟩
      (constructedRouteSegment_mem_drawing_indexedSegments
        graph taggedEdgeMem taggedSegmentMem)
      translate translateNeighbor
  have bendLawsForRoute :
      ∀ routeBend ∈
          routeBends taggedEdge.2 translate points,
        assignment (.inl (.terminal routeBend.incomingTerminal)) =
          assignment
            (.inl (.terminal routeBend.outgoingTerminal)) := by
    intro routeBend routeBendMem
    apply bendLaws (routeBend.equalityLink graph)
    apply List.mem_map.mpr
    refine ⟨routeBend, ?_, rfl⟩
    apply List.mem_dedup.mpr
    apply List.mem_flatMap.mpr
    refine
      ⟨(points, taggedEdge.2),
        constructedEdgeRoute_mem_drawing_edgeRoutes_zipIdx
          graph taggedEdgeMem, ?_⟩
    apply List.mem_flatMap.mpr
    exact
      ⟨translate,
        (mem_neighborTranslations_iff translate).mpr
          translateNeighbor,
        routeBendMem⟩
  cases segmentsEq : segments with
  | nil =>
      exact (segmentsNonempty segmentsEq).elim
  | cons first rest =>
      have propagated :=
        routeTerminals_assignment_eq_aux
          (assignment ∘ Sum.inl) taggedEdge.2 translate
          points 0 first rest
          (by simpa [segments] using segmentsEq)
          (by simpa [segments] using segmentLaws)
          (by simpa [routeBends] using bendLawsForRoute)
      have defaultEq :
          (first :: rest).getLastD default =
            (first :: rest).getLastD first := by
        rw [List.getLastD_cons, List.getLastD_cons]
      rw [← defaultEq] at propagated
      simpa [segments, segmentsEq, points,
        taggedRouteSegmentTerminal] using propagated

/-- A satisfying complete route core propagates one value from the canonical
first terminal to the canonical last terminal of every listed neighboring
protoedge route. -/
theorem drawingRoutePlanarCoreFormula_route_terminal_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (holds :
      FormulaHolds assignment
        (drawingRoutePlanarCoreFormula graph))
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (taggedEdgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate)
    (default : GridSegment × Nat) :
    let segments :=
      (gridPolylineSegments
        (constructedEdgeRoute graph
          taggedEdge.1 taggedEdge.2)).zipIdx
    let first := segments.getD 0 default
    let last := segments.getLastD default
    assignment
        (.inl (.terminal
          (taggedRouteSegmentTerminal taggedEdge.2 translate
            first .start))) =
      assignment
        (.inl (.terminal
          (taggedRouteSegmentTerminal taggedEdge.2 translate
            last .finish))) := by
  have laws :=
    drawingRoutePlanarCoreFormula_boundary_laws
      graph assignment holds
  exact constructedRouteTerminals_assignment_eq
    graph assignment laws.1 laws.2.1 laws.2.2
    taggedEdgeMem translate translateNeighbor default

end PeriodicOrthocrossing
end LeanTrominoes
