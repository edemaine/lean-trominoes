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

/-! ## Endpoint-isolated normalization -/

/-- The first listed point does not occur again later in the route. -/
def HeadNotInTail (points : List Cell) : Prop :=
  ∀ head, points.head? = some head → head ∉ points.tail

/-- The final listed point does not occur earlier in the route. -/
def LastNotInDropLast (points : List Cell) : Prop :=
  ∀ last, points.getLast? = some last → last ∉ points.dropLast

/-- A duplicate-free point list has an isolated first endpoint. -/
theorem headNotInTail_of_nodup
    {points : List Cell}
    (nodup : points.Nodup) :
    HeadNotInTail points := by
  intro head headLookup
  cases points with
  | nil => simp at headLookup
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at headLookup
      subst first
      exact (List.nodup_cons.mp nodup).1

/-- A duplicate-free point list has an isolated final endpoint. -/
theorem lastNotInDropLast_of_nodup
    {points : List Cell}
    (nodup : points.Nodup) :
    LastNotInDropLast points := by
  intro last lastLookup
  have lastMember : last ∈ points.getLast? := by
    simp [lastLookup]
  have decomposition :=
    List.dropLast_append_getLast? last lastMember
  rw [← decomposition] at nodup
  have concatenated : (points.dropLast.concat last).Nodup := by
    simpa [List.concat_eq_append] using nodup
  exact
    (List.nodup_concat points.dropLast last).mp concatenated |>.1

/-- A simple orthogonal route has an isolated first endpoint even after all
of its long segments are subdivided into unit steps. -/
theorem headNotInTail_unitSubdividePolyline_of_simple
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple : LocalIncidenceDrawing.RouteIsSimple points) :
    HeadNotInTail (unitSubdividePolyline points) :=
  headNotInTail_of_nodup
    (unitSubdividePolyline_nodup orthogonal simple)

/-- A simple orthogonal route has an isolated final endpoint even after all
of its long segments are subdivided into unit steps. -/
theorem lastNotInDropLast_unitSubdividePolyline_of_simple
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (simple : LocalIncidenceDrawing.RouteIsSimple points) :
    LastNotInDropLast (unitSubdividePolyline points) :=
  lastNotInDropLast_of_nodup
    (unitSubdividePolyline_nodup orthogonal simple)

/-- Bypass retains the first dart of a nontrivial walk whenever its starting
vertex does not occur in the rest of the walk. -/
private theorem polylineFirstDirection_bypass_support_of_start_fresh
    {source target : Cell}
    (walk : unitAxisGraph.Walk source target)
    (nontrivial : ¬ walk.Nil)
    (fresh : source ∉ walk.support.tail) :
    polylineFirstDirection walk.bypass.support =
      polylineFirstDirection walk.support := by
  cases walk with
  | nil => exact (nontrivial .nil).elim
  | cons adjacent tail =>
      have absent : source ∉ tail.bypass.support := by
        intro member
        exact fresh
          (tail.support_bypass_subset_support member)
      simp only [SimpleGraph.Walk.bypass, dif_neg absent]
      simp only [SimpleGraph.Walk.support_cons]
      rw [← tail.bypass.cons_tail_support,
        ← tail.cons_tail_support]
      rfl

/-- Removing the first entry of a list and then its last entry cannot expose
a point that was not already present before the original last entry. -/
private theorem mem_dropLast_tail_imp_mem_dropLast
    {Item : Type*} {item : Item} {items : List Item}
    (member : item ∈ items.tail.dropLast) :
    item ∈ items.dropLast := by
  cases items with
  | nil => simp at member
  | cons first rest =>
      cases rest with
      | nil => simp at member
      | cons second rest =>
          simpa using List.mem_cons_of_mem first member

/-- In a walk whose endpoint has no earlier occurrence, the only dart ending
at that endpoint is the final dart. -/
private theorem dart_eq_lastDart_of_end_fresh
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : SimpleGraph Vertex}
    {source target : Vertex}
    (walk : graph.Walk source target)
    (nontrivial : ¬ walk.Nil)
    (fresh : target ∉ walk.support.dropLast)
    {dart : graph.Dart}
    (dartMember : dart ∈ walk.darts)
    (dartTarget : dart.snd = target) :
    dart = walk.lastDart nontrivial := by
  by_contra different
  have dartsNonempty : walk.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr nontrivial
  have differentFromLast :
      dart ≠ walk.darts.getLast dartsNonempty := by
    rw [SimpleGraph.Walk.getLast_darts_eq_lastDart]
    exact different
  have beforeLast : dart ∈ walk.darts.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast
      dartMember differentFromLast
  have targetInTailDropLast :
      target ∈ walk.support.tail.dropLast := by
    have mapped :
        dart.snd ∈
          (walk.darts.dropLast).map (fun edge => edge.snd) :=
      List.mem_map.mpr ⟨dart, beforeLast, rfl⟩
    rw [List.map_dropLast,
      SimpleGraph.Walk.map_snd_darts] at mapped
    simpa [dartTarget] using mapped
  exact fresh
    (mem_dropLast_tail_imp_mem_dropLast targetInTailDropLast)

/-- The final directed axis of a nontrivial unit-axis walk is the direction
of its final dart. -/
private theorem polylineLastDirection_support_eq_lastDart
    {source target : Cell}
    (walk : unitAxisGraph.Walk source target)
    (nontrivial : ¬ walk.Nil) :
    polylineLastDirection walk.support =
      between
        (walk.lastDart nontrivial).fst
        (walk.lastDart nontrivial).snd := by
  let leading := walk.dropLast.support.dropLast
  have dropLastDecomposition :
      walk.dropLast.support =
        leading ++ [walk.penultimate] := by
    simp [leading]
  have supportDecomposition :
      walk.support =
        leading ++ [walk.penultimate, target] := by
    calc
      walk.support = walk.dropLast.support ++ [target] :=
        (walk.support_dropLast_concat nontrivial).symm
      _ = (leading ++ [walk.penultimate]) ++ [target] := by
        rw [dropLastDecomposition]
      _ = leading ++ [walk.penultimate, target] := by simp
  rw [supportDecomposition]
  exact
    polylineLastDirection_append_pair leading
      ((unitAxisGraph_adj_iff _ _).mp
        (walk.lastDart nontrivial).adj)

/-- Bypass retains the final dart of a nontrivial walk whenever its target
does not occur before the end. -/
private theorem polylineLastDirection_bypass_support_of_end_fresh
    {source target : Cell}
    (walk : unitAxisGraph.Walk source target)
    (nontrivial : ¬ walk.Nil)
    (fresh : target ∉ walk.support.dropLast) :
    polylineLastDirection walk.bypass.support =
      polylineLastDirection walk.support := by
  have sourceInDropLast : source ∈ walk.support.dropLast := by
    have firstDartMember := walk.firstDart_mem_darts nontrivial
    have mapped :
        (walk.firstDart nontrivial).fst ∈
          walk.darts.map (fun dart => dart.fst) :=
      List.mem_map.mpr
        ⟨walk.firstDart nontrivial, firstDartMember, rfl⟩
    rw [SimpleGraph.Walk.map_fst_darts] at mapped
    simpa using mapped
  have endpointsDifferent : source ≠ target := by
    intro equal
    have targetInDropLast : target ∈ walk.support.dropLast := by
      simpa only [equal] using sourceInDropLast
    exact fresh targetInDropLast
  have bypassNontrivial : ¬ walk.bypass.Nil :=
    SimpleGraph.Walk.not_nil_of_ne endpointsDifferent
  have retainedLastMember :
      walk.bypass.lastDart bypassNontrivial ∈ walk.darts :=
    walk.darts_bypass_subset_darts
      (walk.bypass.lastDart_mem_darts bypassNontrivial)
  have retainedLast :
      walk.bypass.lastDart bypassNontrivial =
        walk.lastDart nontrivial :=
    dart_eq_lastDart_of_end_fresh walk nontrivial fresh
      retainedLastMember rfl
  rw [polylineLastDirection_support_eq_lastDart
      walk.bypass bypassNontrivial,
    polylineLastDirection_support_eq_lastDart
      walk nontrivial,
    retainedLast]

/-- Orthogonal loop erasure preserves the first direction when the unit-
subdivided starting cell does not occur again later. -/
theorem polylineFirstDirection_normalizeOrthogonalPolyline_of_headNotInTail
    {points : List Cell}
    (length : 2 ≤ (unitSubdividePolyline points).length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (fresh : HeadNotInTail (unitSubdividePolyline points)) :
    polylineFirstDirection (normalizeOrthogonalPolyline points) =
      polylineFirstDirection points := by
  have nonempty : points ≠ [] := by
    intro empty
    simp [empty] at length
  let walk := orthogonalUnitWalk nonempty orthogonal
  have walkSupport :
      walk.support = unitSubdividePolyline points := by
    simp [walk, orthogonalUnitWalk]
  have walkNontrivial : ¬ walk.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have supportLength : 2 ≤ walk.support.length := by
      simpa [walkSupport] using length
    rw [SimpleGraph.Walk.length_support] at supportLength
    omega
  have subdividedStartFresh :
      (unitSubdividePolyline points).head
          (unitSubdividePolyline_ne_nil nonempty) ∉
        (unitSubdividePolyline points).tail := by
    apply fresh
      ((unitSubdividePolyline points).head
        (unitSubdividePolyline_ne_nil nonempty))
    exact
      List.head?_eq_some_head
        (unitSubdividePolyline_ne_nil nonempty)
  have startFresh :
      walk.support.head walk.support_ne_nil ∉
        walk.support.tail := by
    simpa only [walkSupport] using subdividedStartFresh
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  change polylineFirstDirection walk.bypass.support =
    polylineFirstDirection points
  calc
    polylineFirstDirection walk.bypass.support =
        polylineFirstDirection walk.support :=
      polylineFirstDirection_bypass_support_of_start_fresh
        walk walkNontrivial
        (by simpa using startFresh)
    _ = polylineFirstDirection (unitSubdividePolyline points) := by
      rw [walkSupport]
    _ = polylineFirstDirection points :=
      polylineFirstDirection_unitSubdividePolyline
        (by
          cases points with
          | nil => simp at nonempty
          | cons first rest =>
              cases rest with
              | nil =>
                  simp at length
              | cons second rest => simp)
        orthogonal

/-- Orthogonal loop erasure preserves the last direction when the unit-
subdivided ending cell does not occur earlier. -/
theorem polylineLastDirection_normalizeOrthogonalPolyline_of_lastNotInDropLast
    {points : List Cell}
    (length : 2 ≤ (unitSubdividePolyline points).length)
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (fresh : LastNotInDropLast (unitSubdividePolyline points)) :
    polylineLastDirection (normalizeOrthogonalPolyline points) =
      polylineLastDirection points := by
  have nonempty : points ≠ [] := by
    intro empty
    simp [empty] at length
  let walk := orthogonalUnitWalk nonempty orthogonal
  have walkSupport :
      walk.support = unitSubdividePolyline points := by
    simp [walk, orthogonalUnitWalk]
  have walkNontrivial : ¬ walk.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have supportLength : 2 ≤ walk.support.length := by
      simpa [walkSupport] using length
    rw [SimpleGraph.Walk.length_support] at supportLength
    omega
  have subdividedEndFresh :
      (unitSubdividePolyline points).getLast
          (unitSubdividePolyline_ne_nil nonempty) ∉
        (unitSubdividePolyline points).dropLast := by
    apply fresh
      ((unitSubdividePolyline points).getLast
        (unitSubdividePolyline_ne_nil nonempty))
    exact
      List.getLast?_eq_getLast_of_ne_nil
        (unitSubdividePolyline_ne_nil nonempty)
  have endFresh :
      walk.support.getLast walk.support_ne_nil ∉
        walk.support.dropLast := by
    simpa only [walkSupport] using subdividedEndFresh
  rw [normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  change polylineLastDirection walk.bypass.support =
    polylineLastDirection points
  calc
    polylineLastDirection walk.bypass.support =
        polylineLastDirection walk.support :=
      polylineLastDirection_bypass_support_of_end_fresh
        walk walkNontrivial
        (by simpa using endFresh)
    _ = polylineLastDirection (unitSubdividePolyline points) := by
      rw [walkSupport]
    _ = polylineLastDirection points :=
      polylineLastDirection_unitSubdividePolyline
        (by
          cases points with
          | nil => simp at nonempty
          | cons first rest =>
              cases rest with
              | nil =>
                  simp at length
              | cons second rest => simp)
        orthogonal

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
