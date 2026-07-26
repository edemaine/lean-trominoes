import LeanTrominoes.PeriodicCNFPlanarOrderedOneInThreePositioned
import LeanTrominoes.PositionedPeriodicCNFIncidenceDrawing
import LeanTrominoes.PositionedPeriodicCNFIncidenceRouteLookup
import Mathlib.Data.List.Sort

/-!
# Occurrence order extracted from incidence-route geometry

Occurrence splitting must connect the copies of a planar variable in the
rotation order of their incident routes.  A positioned incidence
presentation orients every route from its clause to its variable, so the
last route segment determines the direction in which that incidence leaves
the variable when traversed backwards.

This file turns those terminal directions into an executable cyclic order.
Sorting changes only presentation order: the resulting list is proved to be
a permutation of the genuine syntactic occurrence copies and therefore
packages directly as `PeriodicThreeSATThree.OccurrenceOrder`.
-/

namespace LeanTrominoes

namespace PeriodicThreeSATThree

/-- The four directions in cyclic counterclockwise order, followed by a
total fallback for malformed or degenerate routes. -/
inductive TerminalDirection
  | east
  | north
  | west
  | south
  | degenerate
  deriving DecidableEq, Repr

namespace TerminalDirection

/-- Numeric key realizing the declared cyclic order. -/
def rank : TerminalDirection → Nat
  | .east => 0
  | .north => 1
  | .west => 2
  | .south => 3
  | .degenerate => 4

end TerminalDirection

/-- Direction from a route's variable endpoint back along its final
clause-to-variable segment.  Non-axis-aligned, zero-length, and too-short
routes receive the harmless fallback key. -/
def routeTerminalDirection (route : List Cell) : TerminalDirection :=
  match (gridPolylineSegments route).getLast? with
  | none => .degenerate
  | some segment =>
      if segment.start.2 = segment.finish.2 then
        if segment.finish.1 < segment.start.1 then
          .east
        else if segment.start.1 < segment.finish.1 then
          .west
        else
          .degenerate
      else if segment.start.1 = segment.finish.1 then
        if segment.finish.2 < segment.start.2 then
          .north
        else if segment.start.2 < segment.finish.2 then
          .south
        else
          .degenerate
      else
        .degenerate

/-- An axis-aligned final segment always determines one of the four genuine
directions. -/
theorem routeTerminalDirection_ne_degenerate_of_last_axisAligned
    {route : List Cell} {segment : GridSegment}
    (last : (gridPolylineSegments route).getLast? = some segment)
    (aligned : segment.IsAxisAligned) :
    routeTerminalDirection route ≠ .degenerate := by
  unfold routeTerminalDirection
  rw [last]
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at aligned
  rcases aligned with ⟨sameY, differentX⟩ |
      ⟨sameX, differentY⟩
  · subst finishY
    by_cases east : finishX < startX
    · simp [east]
    · have west : startX < finishX := by omega
      simp [east, west]
  · subst finishX
    by_cases north : finishY < startY
    · simp [differentY, north]
    · have south : startY < finishY := by omega
      simp [differentY, north, south]

/-- Every genuine terminal direction has a rank in the four-position cyclic
range. -/
theorem TerminalDirection.rank_lt_four
    {direction : TerminalDirection}
    (genuine : direction ≠ .degenerate) :
    direction.rank < 4 := by
  cases direction <;> simp_all [TerminalDirection.rank]

/-- Terminal direction of the incidence route named by one occurrence
copy's clause and literal indices. -/
def occurrenceTerminalDirection
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable) :
    TerminalDirection :=
  routeTerminalDirection (routes copy.2.1 copy.2.2)

/-- Every genuine occurrence copy determines the matching metadata-rich
incidence at the same clause and literal indices. -/
theorem exists_taggedIncidence_of_mem_occurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (copy : ThreeOccurrenceVariable Variable)
    (copyMember : copy ∈ occurrenceVariables source atom) :
    ∃ tagged :
        CNFIncidence Variable × Nat,
      tagged ∈
          (PeriodicCNF.incidencesWithMetadata source).zipIdx ∧
        tagged.1.clauseIndex = copy.2.1 ∧
        tagged.1.literalIndex = copy.2.2 := by
  simp only [occurrenceVariables, List.mem_filterMap] at copyMember
  rcases copyMember with
    ⟨taggedLiteral, taggedLiteralMember, selected⟩
  split at selected
  · simp only [Option.some.injEq] at selected
    subst copy
    simp only [taggedLiterals, List.mem_flatMap,
      List.mem_map] at taggedLiteralMember
    rcases taggedLiteralMember with
      ⟨taggedClause, taggedClauseMember,
        sourceTaggedLiteral, sourceTaggedLiteralMember,
        taggedLiteralEq⟩
    subst taggedLiteral
    let incidence : CNFIncidence Variable :=
      ⟨taggedClause.2, taggedClause.1,
        sourceTaggedLiteral.2, sourceTaggedLiteral.1⟩
    have incidenceMember :
        incidence ∈
          PeriodicCNF.incidencesWithMetadata source := by
      simp only [PeriodicCNF.incidencesWithMetadata,
        List.mem_flatMap, List.mem_map]
      exact
        ⟨taggedClause, taggedClauseMember,
          sourceTaggedLiteral, sourceTaggedLiteralMember, rfl⟩
    rcases List.mem_iff_getElem.mp incidenceMember with
      ⟨index, indexLt, incidenceAt⟩
    refine ⟨(incidence, index), ?_, rfl, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨indexLt, incidenceAt⟩
  · contradiction

/-- Every final segment of the certified route belonging to a genuine
occurrence copy is axis-aligned. -/
theorem occurrence_route_last_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.PlanarIncidencePresentation
        source placement)
    (atom : Variable) (copy : ThreeOccurrenceVariable Variable)
    (copyMember :
      copy ∈ occurrenceVariables source.erase atom)
    {segment : GridSegment}
    (last :
      (gridPolylineSegments
        (presentation.routes copy.2.1 copy.2.2)).getLast? =
          some segment) :
    segment.IsAxisAligned := by
  rcases
      exists_taggedIncidence_of_mem_occurrenceVariables
        source.erase atom copy copyMember with
    ⟨tagged, taggedMember, clauseIndex, literalIndex⟩
  have routeOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (presentation.routes copy.2.1 copy.2.2) :=
    by
      have taggedRouteOrthogonal :=
        presentation.route_orthogonal_of_tagged taggedMember
      simpa [clauseIndex, literalIndex] using
        taggedRouteOrthogonal
  apply
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments
      (presentation.routes copy.2.1 copy.2.2)).mp
      routeOrthogonal
  have segmentLastMember :
      segment ∈
        (gridPolylineSegments
          (presentation.routes copy.2.1 copy.2.2)).getLast? := by
    rw [last]
    simp
  rcases List.mem_getLast?_eq_getLast segmentLastMember with
    ⟨segmentsNonempty, segmentEq⟩
  rw [segmentEq]
  exact List.getLast_mem segmentsNonempty

/-- A certified occurrence route with a final segment receives one of the
four genuine cyclic direction keys. -/
theorem occurrenceTerminalDirection_ne_degenerate
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.PlanarIncidencePresentation
        source placement)
    (atom : Variable) (copy : ThreeOccurrenceVariable Variable)
    (copyMember :
      copy ∈ occurrenceVariables source.erase atom)
    {segment : GridSegment}
    (last :
      (gridPolylineSegments
        (presentation.routes copy.2.1 copy.2.2)).getLast? =
          some segment) :
    occurrenceTerminalDirection presentation.routes copy ≠
      .degenerate := by
  exact
    routeTerminalDirection_ne_degenerate_of_last_axisAligned
      last
      (occurrence_route_last_axisAligned
        presentation atom copy copyMember last)

/-- Boolean comparison used to sort occurrence copies cyclically around
their common variable endpoint. -/
def occurrenceDirectionLE
    {Variable : Type*}
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable) : Bool :=
  decide
    ((occurrenceTerminalDirection routes first).rank ≤
      (occurrenceTerminalDirection routes second).rank)

/-- Genuine copies of one variable sorted by their terminal route
directions.  Merge sort is stable, so any fallback ties retain presentation
order. -/
def geometricOccurrenceVariables
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    List (ThreeOccurrenceVariable Variable) :=
  (occurrenceVariables source atom).mergeSort
    (occurrenceDirectionLE routes)

/-- Direction sorting preserves exactly the source variable's genuine
syntactic occurrence copies. -/
theorem geometricOccurrenceVariables_perm
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (geometricOccurrenceVariables source routes atom).Perm
      (occurrenceVariables source atom) := by
  exact List.mergeSort_perm _ _

/-- The extracted list is monotonically ordered by cyclic direction rank. -/
theorem geometricOccurrenceVariables_pairwise
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (geometricOccurrenceVariables source routes atom).Pairwise
      (fun first second =>
        (occurrenceTerminalDirection routes first).rank ≤
          (occurrenceTerminalDirection routes second).rank) := by
  unfold geometricOccurrenceVariables
  have sorted :=
    List.pairwise_mergeSort
      (le := occurrenceDirectionLE routes)
      (fun first second third firstLe secondLe => by
        simp only [occurrenceDirectionLE, decide_eq_true_eq] at firstLe secondLe
        simp only [occurrenceDirectionLE, decide_eq_true_eq]
        omega)
      (fun first second => by
        simp only [occurrenceDirectionLE, Bool.or_eq_true, decide_eq_true_eq]
        omega)
      (occurrenceVariables source atom)
  simpa only [occurrenceDirectionLE, decide_eq_true_eq] using sorted

/-- A lawful occurrence order extracted from the terminal directions of a
route family. -/
def geometricOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    OccurrenceOrder source where
  copies := geometricOccurrenceVariables source routes
  perm := geometricOccurrenceVariables_perm source routes

@[simp]
theorem geometricOccurrenceOrder_copies
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (atom : Variable) :
    (geometricOccurrenceOrder source routes).copies atom =
      geometricOccurrenceVariables source routes atom := by
  rfl

end PeriodicThreeSATThree

namespace PositionedPeriodicCNF

/-- Extract the lawful rotation order carried by a certified planar
incidence presentation.  The permutation property needs only its route
family; planarity will justify the later local cycle routing. -/
def PlanarIncidencePresentation.occurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) :
    PeriodicThreeSATThree.OccurrenceOrder source.erase :=
  PeriodicThreeSATThree.geometricOccurrenceOrder
    source.erase presentation.routes

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

/-- Specialize geometric order extraction to the wrapped routed planar SAT
formula that feeds the positioned exact-one pipeline. -/
def drawingOccurrenceOrderOfPresentation
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (presentation :
      PositionedPeriodicCNF.PlanarIncidencePresentation
        (wrappedDrawingPositionedPeriodicPlanarSATFormula formula)
        (wrappedDrawingPeriodicPlanarSATPlacement formula)) :
    DrawingOccurrenceOrder formula :=
  presentation.occurrenceOrder

end PeriodicOrthocrossing

end LeanTrominoes
