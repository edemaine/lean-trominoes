import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Segment occurrences in the periodic track construction

The drawing API indexes routes after they have been constructed.  For the
global crossing proof it is more convenient to expose the equivalent
edge-first enumeration, in which every segment retains the protoedge that
created it.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- All constructed segments, indexed directly by their protoedge and their
position within that edge route. -/
def constructedIndexedSegments {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List IndexedGridSegment :=
  graph.edges.zipIdx.zipIdx.flatMap fun taggedRoute =>
    (gridPolylineSegments
      (constructedEdgeRoute graph
        taggedRoute.1.1 taggedRoute.1.2)).zipIdx.map
        fun taggedSegment =>
          ⟨taggedRoute.2, taggedSegment.2, taggedSegment.1⟩

/-- Indexing the completed route list agrees with indexing each route at the
protoedge that generated it. -/
theorem drawing_indexedSegments_eq_constructed {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    (drawing graph).indexedSegments = constructedIndexedSegments graph := by
  simp [PeriodicGridDrawing.indexedSegments, drawing,
    constructedEdgeRoutes, constructedIndexedSegments, List.zipIdx_map,
    List.flatMap_map]

/-- Membership in the generated segment list exposes both the originating
indexed protoedge and the segment's within-route index. -/
theorem mem_drawing_indexedSegments_iff {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment} :
    indexed ∈ (drawing graph).indexedSegments ↔
      ∃ taggedRoute ∈ graph.edges.zipIdx.zipIdx,
        ∃ taggedSegment ∈
            (gridPolylineSegments
              (constructedEdgeRoute graph
                taggedRoute.1.1 taggedRoute.1.2)).zipIdx,
          indexed =
            ⟨taggedRoute.2, taggedSegment.2, taggedSegment.1⟩ := by
  rw [drawing_indexedSegments_eq_constructed]
  simp [constructedIndexedSegments, eq_comm]

/-- The second index attached by re-indexing `zipIdx` is the original index.
This lets the crossing proof freely move between route and protoedge indices. -/
theorem nested_zipIdx_indices_eq {α : Type*} {values : List α}
    {tagged : (α × Nat) × Nat}
    (taggedMem : tagged ∈ values.zipIdx.zipIdx) :
    tagged.1.2 = tagged.2 := by
  have atIndex := congrArg Prod.snd (List.mem_zipIdx' taggedMem).2
  simpa using atIndex

/-- A representative in one half-open period and its integer translate are
unique.  This is the arithmetic basis for all private-lane arguments. -/
theorem periodic_coordinate_unique
    {period first second firstShift secondShift : Int}
    (periodPositive : 0 < period)
    (firstBounds : 0 ≤ first ∧ first < period)
    (secondBounds : 0 ≤ second ∧ second < period)
    (equal :
      first + period * firstShift =
        second + period * secondShift) :
    first = second ∧ firstShift = secondShift := by
  have firstRemainder :
      (first + period * firstShift) % period = first := by
    rw [Int.add_emod]
    simp [Int.emod_eq_of_lt firstBounds.1 firstBounds.2]
  have secondRemainder :
      (second + period * secondShift) % period = second := by
    rw [Int.add_emod]
    simp [Int.emod_eq_of_lt secondBounds.1 secondBounds.2]
  have sameRemainder :=
    congrArg (fun coordinate : Int => coordinate % period) equal
  rw [firstRemainder, secondRemainder] at sameRemainder
  constructor
  · exact sameRemainder
  · subst second
    have productsEqual :
        period * firstShift = period * secondShift :=
      Int.add_left_cancel equal
    exact mul_left_cancel₀ (ne_of_gt periodPositive) productsEqual

/-- Two horizontal segment interiors containing the same point lie on the
same horizontal line. -/
theorem horizontal_lanes_eq_of_interior_contains
    {first second : GridSegment} {point : Cell}
    (firstContains : first.InteriorContains point)
    (secondContains : second.InteriorContains point)
    (firstHorizontal : first.IsHorizontal)
    (secondHorizontal : second.IsHorizontal) :
    first.start.2 = second.start.2 := by
  rcases firstContains with firstContains | firstContains
  · rcases secondContains with secondContains | secondContains
    · omega
    · simp [GridSegment.IsHorizontal, GridSegment.IsVertical]
        at firstHorizontal secondHorizontal secondContains
      omega
  · simp [GridSegment.IsHorizontal, GridSegment.IsVertical]
      at firstHorizontal firstContains
    omega

/-- Two vertical segment interiors containing the same point lie on the same
vertical line. -/
theorem vertical_lanes_eq_of_interior_contains
    {first second : GridSegment} {point : Cell}
    (firstContains : first.InteriorContains point)
    (secondContains : second.InteriorContains point)
    (firstVertical : first.IsVertical)
    (secondVertical : second.IsVertical) :
    first.start.1 = second.start.1 := by
  rcases firstContains with firstContains | firstContains
  · simp [GridSegment.IsHorizontal, GridSegment.IsVertical]
      at firstContains firstVertical
    omega
  · rcases secondContains with secondContains | secondContains
    · simp [GridSegment.IsHorizontal, GridSegment.IsVertical]
        at secondContains secondVertical
      omega
    · omega

/-- Once the axes differ, common interior containment is exactly a proper
orthogonal crossing. -/
theorem properlyCrossesAt_of_different_axes
    {first second : GridSegment} {point : Cell}
    (firstContains : first.InteriorContains point)
    (secondContains : second.InteriorContains point)
    (axes :
      (first.IsHorizontal ∧ second.IsVertical) ∨
        (first.IsVertical ∧ second.IsHorizontal)) :
    GridSegment.ProperlyCrossesAt first second point :=
  ⟨firstContains, secondContains, axes⟩

end PeriodicOrthocrossing
end LeanTrominoes
