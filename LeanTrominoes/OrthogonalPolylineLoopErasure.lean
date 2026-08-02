import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionSimplicity
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Loop erasure for orthogonal lattice polylines

Some routed constructions are naturally certified as orthogonal walks rather
than simple paths: their listed points may revisit a lattice cell.  Before a
route is thickened into a ribbon, this module first subdivides it into unit
axis steps and then applies `SimpleGraph.Walk.bypass`.  The result has the same
endpoints, has no repeated point, and uses only directed unit edges of the
subdivided source route.
-/

namespace LeanTrominoes
namespace AxisDirection

/-- The simple graph whose edges are the four undirected unit lattice steps. -/
def unitAxisGraph : SimpleGraph Cell :=
  SimpleGraph.fromRel IsUnitAxisStep

/-- A genuine unit step has distinct endpoints. -/
theorem IsUnitAxisStep.ne
    {source target : Cell}
    (unit : IsUnitAxisStep source target) :
    source ≠ target := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rcases source with ⟨horizontal, vertical⟩
  cases direction <;>
    simp_all [IsGenuine, step, Cell.add]

/-- Adjacency in `unitAxisGraph` is exactly an oriented unit axis step. -/
@[simp]
theorem unitAxisGraph_adj_iff
    (source target : Cell) :
    unitAxisGraph.Adj source target ↔
      IsUnitAxisStep source target := by
  constructor
  · rintro ⟨_, unit | unit⟩
    · exact unit
    · exact unit.symm
  · intro unit
    exact ⟨unit.ne, Or.inl unit⟩

/-- Unit subdivision of a nonempty route remains nonempty. -/
theorem unitSubdividePolyline_ne_nil
    {points : List Cell}
    (nonempty : points ≠ []) :
    unitSubdividePolyline points ≠ [] := by
  cases points with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      intro empty
      have head :=
        unitSubdividePolyline_head?
          (points := first :: rest) (by simp)
      rw [empty] at head
      simp at head

/-- Regard an orthogonal lattice polyline as a walk in the unit-axis graph,
after inserting every intermediate lattice point. -/
def orthogonalUnitWalk
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    unitAxisGraph.Walk
      ((unitSubdividePolyline points).head
        (unitSubdividePolyline_ne_nil nonempty))
      ((unitSubdividePolyline points).getLast
        (unitSubdividePolyline_ne_nil nonempty)) :=
  SimpleGraph.Walk.ofSupport
    (unitSubdividePolyline points)
    (unitSubdividePolyline_ne_nil nonempty)
    ((unitSubdividePolyline_unitSteps orthogonal).imp
      fun _ _ unit => (unitAxisGraph_adj_iff _ _).mpr unit)

/-- Subdivide an orthogonal route and erase every loop in the resulting unit
walk.  Proof irrelevance makes the output depend only on `points`. -/
def eraseOrthogonalLoops
    (points : List Cell)
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    List Cell :=
  (orthogonalUnitWalk nonempty orthogonal).bypass.support

/-- Loop erasure never returns the empty route. -/
theorem eraseOrthogonalLoops_ne_nil
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    eraseOrthogonalLoops points nonempty orthogonal ≠ [] := by
  exact SimpleGraph.Walk.support_ne_nil _

/-- The loop-erased route has no repeated lattice point. -/
theorem eraseOrthogonalLoops_nodup
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (eraseOrthogonalLoops points nonempty orthogonal).Nodup := by
  exact
    (SimpleGraph.Walk.isPath_def _).mp
      (SimpleGraph.Walk.bypass_isPath
        (orthogonalUnitWalk nonempty orthogonal))

/-- Every consecutive pair in the loop-erased route is still a genuine unit
axis step. -/
theorem eraseOrthogonalLoops_unitSteps
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (eraseOrthogonalLoops points nonempty orthogonal).IsChain
      IsUnitAxisStep := by
  exact
    (SimpleGraph.Walk.isChain_adj_support
      (orthogonalUnitWalk nonempty orthogonal).bypass).imp
        fun _ _ adjacent =>
          (unitAxisGraph_adj_iff _ _).mp adjacent

/-- Loop erasure selects a sublist of the unit-subdivided route's points. -/
theorem eraseOrthogonalLoops_sublist_unitSubdividePolyline
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    List.Sublist
      (eraseOrthogonalLoops points nonempty orthogonal)
      (unitSubdividePolyline points) := by
  simpa only [eraseOrthogonalLoops, orthogonalUnitWalk,
    SimpleGraph.Walk.support_ofSupport] using
      (orthogonalUnitWalk nonempty orthogonal
        |>.support_bypass_sublist_support)

/-- More strongly, every directed edge retained by loop erasure is an edge
of the unit-subdivided source walk. -/
theorem eraseOrthogonalLoops_darts_sublist
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    List.Sublist
      (orthogonalUnitWalk nonempty orthogonal).bypass.darts
      (orthogonalUnitWalk nonempty orthogonal).darts :=
  SimpleGraph.Walk.darts_bypass_sublist_darts _

/-- Loop erasure preserves the first advertised endpoint. -/
theorem eraseOrthogonalLoops_head?
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (eraseOrthogonalLoops points nonempty orthogonal).head? =
      points.head? := by
  let walk := orthogonalUnitWalk nonempty orthogonal
  change walk.bypass.support.head? = points.head?
  rw [List.head?_eq_some_head walk.bypass.support_ne_nil,
    SimpleGraph.Walk.head_support]
  rw [← List.head?_eq_some_head
    (unitSubdividePolyline_ne_nil nonempty)]
  exact unitSubdividePolyline_head? nonempty

/-- Loop erasure preserves the last advertised endpoint. -/
theorem eraseOrthogonalLoops_getLast?
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (eraseOrthogonalLoops points nonempty orthogonal).getLast? =
      points.getLast? := by
  let walk := orthogonalUnitWalk nonempty orthogonal
  change walk.bypass.support.getLast? = points.getLast?
  rw [List.getLast?_eq_getLast_of_ne_nil
      walk.bypass.support_ne_nil,
    SimpleGraph.Walk.getLast_support]
  rw [← List.getLast?_eq_getLast_of_ne_nil
    (unitSubdividePolyline_ne_nil nonempty)]
  exact unitSubdividePolyline_getLast? nonempty orthogonal

/-! ## Geometric simplicity -/

/-- The relative interiors of two unit lattice edges can meet only when the
two edges are the same undirected graph edge. -/
theorem unitAxisSteps_edge_eq_of_interiorsMeet
    {firstStart firstFinish secondStart secondFinish : Cell}
    (firstUnit : IsUnitAxisStep firstStart firstFinish)
    (secondUnit : IsUnitAxisStep secondStart secondFinish)
    (meet :
      GridSegment.InteriorsMeet
        (GridSegment.mk firstStart firstFinish)
        (GridSegment.mk secondStart secondFinish)) :
    s(firstStart, firstFinish) =
      s(secondStart, secondFinish) := by
  rcases firstUnit with
    ⟨firstDirection, firstGenuine, rfl⟩
  rcases secondUnit with
    ⟨secondDirection, secondGenuine, rfl⟩
  rcases firstStart with ⟨firstX, firstY⟩
  rcases secondStart with ⟨secondX, secondY⟩
  cases firstDirection <;> cases secondDirection <;>
    simp_all [IsGenuine, step, Cell.add,
      GridSegment.InteriorsMeet,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween] <;>
    omega

/-- The graph-edge list of a walk is the undirected image of the consecutive
grid segments of its support. -/
theorem gridPolylineSegments_map_edge_of_walk
    {source target : Cell}
    (walk : unitAxisGraph.Walk source target) :
    (gridPolylineSegments walk.support).map
        (fun segment => s(segment.start, segment.finish)) =
      walk.edges := by
  induction walk with
  | nil => simp [gridPolylineSegments]
  | cons adjacent tail induction =>
      cases tail with
      | nil => simp [gridPolylineSegments]
      | cons next rest =>
          simp [gridPolylineSegments] at induction ⊢
          exact induction

/-- The support of a path in the unit-axis graph is a geometrically simple
orthogonal route. -/
theorem routeIsSimple_support_of_unitAxisPath
    {source target : Cell}
    {walk : unitAxisGraph.Walk source target}
    (path : walk.IsPath) :
    LocalIncidenceDrawing.RouteIsSimple walk.support := by
  have pointsNodup : walk.support.Nodup := path.support_nodup
  have unitSteps : walk.support.IsChain IsUnitAxisStep :=
    walk.isChain_adj_support.imp fun _ _ adjacent =>
      (unitAxisGraph_adj_iff _ _).mp adjacent
  have segmentUnits :=
    (unitSteps_iff_segments walk.support).mp unitSteps
  refine ⟨pointsNodup, ?_, ?_⟩
  · intro point pointMember segment segmentMember
    exact (segmentUnits segment segmentMember).not_interiorContains
  · intro first firstMember second secondMember
      indicesDifferent interiorsMeet
    have firstUnit :=
      segmentUnits first.1
        (List.fst_mem_of_mem_zipIdx firstMember)
    have secondUnit :=
      segmentUnits second.1
        (List.fst_mem_of_mem_zipIdx secondMember)
    have edgesEqual :=
      unitAxisSteps_edge_eq_of_interiorsMeet
        firstUnit secondUnit interiorsMeet
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff] at firstMember secondMember
    rcases firstMember with ⟨firstSegmentLt, firstSegmentAt⟩
    rcases secondMember with ⟨secondSegmentLt, secondSegmentAt⟩
    have edgeListEqual :=
      gridPolylineSegments_map_edge_of_walk walk
    have firstEdgeLt : first.2 < walk.edges.length := by
      rw [← edgeListEqual, List.length_map]
      exact firstSegmentLt
    have secondEdgeLt : second.2 < walk.edges.length := by
      rw [← edgeListEqual, List.length_map]
      exact secondSegmentLt
    have firstEdgeLookup :
        walk.edges[first.2]? =
          some s(first.1.start, first.1.finish) := by
      rw [← edgeListEqual, List.getElem?_map,
        List.getElem?_eq_getElem firstSegmentLt,
        firstSegmentAt]
      rfl
    have secondEdgeLookup :
        walk.edges[second.2]? =
          some s(second.1.start, second.1.finish) := by
      rw [← edgeListEqual, List.getElem?_map,
        List.getElem?_eq_getElem secondSegmentLt,
        secondSegmentAt]
      rfl
    have firstEdgeAt :
        walk.edges[first.2] =
          s(first.1.start, first.1.finish) := by
      rw [List.getElem?_eq_getElem firstEdgeLt] at firstEdgeLookup
      exact Option.some.inj firstEdgeLookup
    have secondEdgeAt :
        walk.edges[second.2] =
          s(second.1.start, second.1.finish) := by
      rw [List.getElem?_eq_getElem secondEdgeLt] at secondEdgeLookup
      exact Option.some.inj secondEdgeLookup
    have edgeValuesEqual :
        walk.edges[first.2] = walk.edges[second.2] :=
      firstEdgeAt.trans (edgesEqual.trans secondEdgeAt.symm)
    have edgeIndicesEqual : first.2 = second.2 :=
      (SimpleGraph.Walk.edges_nodup_of_support_nodup
          pointsNodup
        |>.getElem_inj_iff).mp edgeValuesEqual
    exact indicesDifferent edgeIndicesEqual

/-- The loop-erased output is therefore simple, despite any repeated points
or self-overlaps in the original orthogonal walk. -/
theorem eraseOrthogonalLoops_isSimple
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    LocalIncidenceDrawing.RouteIsSimple
      (eraseOrthogonalLoops points nonempty orthogonal) := by
  exact routeIsSimple_support_of_unitAxisPath
    (SimpleGraph.Walk.bypass_isPath
      (orthogonalUnitWalk nonempty orthogonal))

/-! ## Total normalization interface -/

/-- A chain of genuine unit axis steps is orthogonal. -/
theorem orthogonalPolyline_of_unitSteps
    {points : List Cell}
    (unitSteps : points.IsChain IsUnitAxisStep) :
    PeriodicOrthocrossing.OrthogonalPolyline points := by
  exact unitSteps.imp fun _ _ unit => by
    rcases unit with ⟨direction, genuine, rfl⟩
    rcases ‹Cell› with ⟨horizontal, vertical⟩
    cases direction <;>
      simp_all [IsGenuine, step, Cell.add,
        GridSegment.IsAxisAligned,
        GridSegment.IsHorizontal, GridSegment.IsVertical]

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- Total computable route normalization.  Empty and nonorthogonal inputs are
left harmlessly unchanged; every nonempty orthogonal input is unit-subdivided
and loop-erased. -/
def normalizeOrthogonalPolyline
    (points : List Cell) : List Cell :=
  if nonempty : points ≠ [] then
    if orthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline points then
      eraseOrthogonalLoops points nonempty orthogonal
    else
      points
  else
    []

/-- The total normalizer selects the certified loop-erasure branch on every
nonempty orthogonal route. -/
theorem normalizeOrthogonalPolyline_eq_erase
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    normalizeOrthogonalPolyline points =
      eraseOrthogonalLoops points nonempty orthogonal := by
  simp only [normalizeOrthogonalPolyline, dif_pos nonempty,
    dif_pos orthogonal]

/-- Normalization preserves the first endpoint of a nonempty orthogonal
route. -/
theorem normalizeOrthogonalPolyline_head?
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (normalizeOrthogonalPolyline points).head? = points.head? := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_head? nonempty orthogonal

/-- Normalization preserves the last endpoint of a nonempty orthogonal
route. -/
theorem normalizeOrthogonalPolyline_getLast?
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (normalizeOrthogonalPolyline points).getLast? =
      points.getLast? := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_getLast? nonempty orthogonal

/-- Normalization of a nonempty orthogonal route is nonempty. -/
theorem normalizeOrthogonalPolyline_ne_nil
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    normalizeOrthogonalPolyline points ≠ [] := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_ne_nil nonempty orthogonal

/-- Normalization exposes a duplicate-free unit-step path. -/
theorem normalizeOrthogonalPolyline_unitSteps
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    (normalizeOrthogonalPolyline points).IsChain
      IsUnitAxisStep := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_unitSteps nonempty orthogonal

/-- The normalized route remains orthogonal. -/
theorem normalizeOrthogonalPolyline_orthogonal
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (normalizeOrthogonalPolyline points) :=
  orthogonalPolyline_of_unitSteps
    (normalizeOrthogonalPolyline_unitSteps nonempty orthogonal)

/-- The normalized route is geometrically simple. -/
theorem normalizeOrthogonalPolyline_isSimple
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    LocalIncidenceDrawing.RouteIsSimple
      (normalizeOrthogonalPolyline points) := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_isSimple nonempty orthogonal

/-- Every normalized point was already present in the unit subdivision of
the source route. -/
theorem normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points) :
    List.Sublist (normalizeOrthogonalPolyline points)
      (unitSubdividePolyline points) := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_sublist_unitSubdividePolyline
    nonempty orthogonal

/-! ## Normalization of already simple routes -/

/-- Bypass changes nothing when its input walk is already a path. -/
private theorem bypass_eq_self_of_isPath
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : SimpleGraph Vertex}
    {source target : Vertex}
    (walk : graph.Walk source target)
    (path : walk.IsPath) :
    walk.bypass = walk := by
  induction walk with
  | nil => rfl
  | cons adjacent tail induction =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at path
      simp [SimpleGraph.Walk.bypass,
        induction path.1, path.2]

/-- On a geometrically simple orthogonal route, normalization performs only
ordered unit subdivision: there are no loops for `bypass` to erase. -/
theorem normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple :
      LocalIncidenceDrawing.RouteIsSimple points) :
    normalizeOrthogonalPolyline points =
      unitSubdividePolyline points := by
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  let walk := orthogonalUnitWalk nonempty orthogonal
  have path : walk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [walk, orthogonalUnitWalk] using
      unitSubdividePolyline_nodup orthogonal simple
  unfold eraseOrthogonalLoops
  rw [bypass_eq_self_of_isPath walk path]
  simp [walk, orthogonalUnitWalk]

/-- Normalization preserves the first directed axis of every nondegenerate
simple orthogonal route. -/
theorem polylineFirstDirection_normalizeOrthogonalPolyline_of_simple
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple :
      LocalIncidenceDrawing.RouteIsSimple points) :
    polylineFirstDirection (normalizeOrthogonalPolyline points) =
      polylineFirstDirection points := by
  have nonempty : points ≠ [] := by
    intro empty
    simp [empty] at length
  rw [normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
    nonempty orthogonal simple]
  exact polylineFirstDirection_unitSubdividePolyline
    length orthogonal

/-- Normalization preserves the final directed axis of every nondegenerate
simple orthogonal route. -/
theorem polylineLastDirection_normalizeOrthogonalPolyline_of_simple
    {points : List Cell}
    (length : 2 ≤ points.length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple :
      LocalIncidenceDrawing.RouteIsSimple points) :
    polylineLastDirection (normalizeOrthogonalPolyline points) =
      polylineLastDirection points := by
  have nonempty : points ≠ [] := by
    intro empty
    simp [empty] at length
  rw [normalizeOrthogonalPolyline_eq_unitSubdividePolyline_of_simple
    nonempty orthogonal simple]
  exact polylineLastDirection_unitSubdividePolyline
    length orthogonal

end AxisDirection
end LeanTrominoes
