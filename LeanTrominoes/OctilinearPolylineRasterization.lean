import LeanTrominoes.OctilinearRayStaircase
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Rasterizing octilinear polylines

This file lifts the eight-direction ray staircase to arbitrary polylines.
Every axis or 45-degree segment is replaced independently, and adjacent
replacements are joined at their common source vertex.  A certified
octilinear polyline therefore produces one orthogonal polyline with exactly
the same outer endpoints.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

/-- Every nondegenerate segment of a polyline lies on one of the eight
compass rays. -/
def OctilinearPolyline (points : List Cell) : Prop :=
  ∀ segment ∈ gridPolylineSegments points,
    (terminalPort
      (Cell.sub segment.finish segment.start)).isSome

instance (points : List Cell) :
    Decidable (OctilinearPolyline points) := by
  unfold OctilinearPolyline
  infer_instance

/-- Rasterize one segment.  The fallback is useful for totality; genuine
octilinear segments are proved below to take the compass-ray branch. -/
def rasterizeSegment (segment : GridSegment) : List Cell :=
  match
      terminalPort
        (Cell.sub segment.finish segment.start) with
  | none => [segment.start, segment.finish]
  | some port =>
      compassRay port
        (compassLength port
          (Cell.sub segment.finish segment.start))
        segment.start

@[simp]
theorem rasterizeSegment_head? (segment : GridSegment) :
    (rasterizeSegment segment).head? = some segment.start := by
  unfold rasterizeSegment
  generalize classified :
    terminalPort (Cell.sub segment.finish segment.start) =
      classifiedPort
  cases classifiedPort <;>
    simp

@[simp]
theorem rasterizeSegment_getLast? (segment : GridSegment) :
    (rasterizeSegment segment).getLast? =
      some segment.finish := by
  unfold rasterizeSegment
  generalize classified :
    terminalPort (Cell.sub segment.finish segment.start) =
      classifiedPort
  cases classifiedPort with
  | none =>
      simp
  | some port =>
      change
        (compassRay port
          (compassLength port
            (Cell.sub segment.finish segment.start))
          segment.start).getLast? =
            some segment.finish
      rw [compassRay_getLast?]
      have decomposition :=
        (compassLength_pos_and_scale classified).2
      apply congrArg some
      rw [← decomposition]
      apply Prod.ext <;>
        simp [Cell.add, Cell.sub]

/-- A successfully classified segment rasterizes to an orthogonal
polyline. -/
theorem rasterizeSegment_orthogonal
    (segment : GridSegment)
    (octilinear :
      (terminalPort
        (Cell.sub segment.finish segment.start)).isSome) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizeSegment segment) := by
  unfold rasterizeSegment
  generalize classified :
    terminalPort (Cell.sub segment.finish segment.start) =
      classifiedPort
  cases classifiedPort with
  | none =>
      simp [classified] at octilinear
  | some port =>
      change
        PeriodicOrthocrossing.OrthogonalPolyline
          (compassRay port
            (compassLength port
              (Cell.sub segment.finish segment.start))
            segment.start)
      exact compassRay_orthogonal port
        (compassLength port
          (Cell.sub segment.finish segment.start))
        segment.start

/-- Replace every consecutive source segment by its compass-ray
rasterization, joining at the original listed vertices. -/
def rasterizePolyline : List Cell → List Cell
  | [] => []
  | first :: rest =>
      match rest with
      | [] => [first]
      | second :: _tail =>
          joinAtEndpoint
            (rasterizeSegment
              (GridSegment.mk first second))
            (rasterizePolyline rest)

@[simp]
theorem rasterizePolyline_nil :
    rasterizePolyline [] = [] := by
  rw [rasterizePolyline]

@[simp]
theorem rasterizePolyline_singleton (point : Cell) :
    rasterizePolyline [point] = [point] := by
  rw [rasterizePolyline]

@[simp]
theorem rasterizePolyline_cons_cons
    (first second : Cell) (rest : List Cell) :
    rasterizePolyline (first :: second :: rest) =
      joinAtEndpoint
        (rasterizeSegment (GridSegment.mk first second))
        (rasterizePolyline (second :: rest)) := by
  rfl

/-- Rasterization preserves the first endpoint, including the empty case. -/
@[simp]
theorem rasterizePolyline_head? (points : List Cell) :
    (rasterizePolyline points).head? = points.head? := by
  induction points using List.twoStepInduction with
  | nil =>
      simp
  | singleton point =>
      simp
  | cons_cons first second rest _ induction =>
      rw [rasterizePolyline_cons_cons]
      simpa using
        joinAtEndpoint_head?
          (rasterizeSegment_head?
            (GridSegment.mk first second))

/-- Rasterization preserves the final endpoint, including the empty case. -/
@[simp]
theorem rasterizePolyline_getLast? (points : List Cell) :
    (rasterizePolyline points).getLast? = points.getLast? := by
  induction points using List.twoStepInduction with
  | nil =>
      simp
  | singleton point =>
      simp
  | cons_cons first second rest _ induction =>
      rw [rasterizePolyline_cons_cons]
      let target :=
        (second :: rest).getLast (by simp)
      have sourceLast :
          (second :: rest).getLast? = some target := by
        rw [List.getLast?_eq_some_getLast]
      have rasterizedLast :
          (rasterizePolyline
            (second :: rest)).getLast? =
              some target := by
        rw [induction second, sourceLast]
      have joinedLast :=
        joinAtEndpoint_getLast?
          (rasterizeSegment_getLast?
            (GridSegment.mk first second))
          (by
            rw [rasterizePolyline_head?]
            rfl)
          rasterizedLast
      rw [joinedLast, List.getLast?_cons_cons,
        sourceLast]

/-- Removing the first source point preserves octilinearity. -/
theorem OctilinearPolyline.tail
    {points : List Cell}
    (octilinear : OctilinearPolyline points) :
    OctilinearPolyline points.tail := by
  cases points with
  | nil =>
      intro segment segmentMember
      simp [gridPolylineSegments] at segmentMember
  | cons first rest =>
      cases rest with
      | nil =>
          intro segment segmentMember
          simp [gridPolylineSegments] at segmentMember
      | cons second rest =>
          intro segment segmentMember
          exact octilinear segment
            (List.mem_cons_of_mem _ segmentMember)

/-- Rasterizing every segment of an octilinear polyline yields one
orthogonal polyline. -/
theorem rasterizePolyline_orthogonal
    {points : List Cell}
    (octilinear : OctilinearPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizePolyline points) := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | singleton point =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | cons_cons first second rest _ induction =>
      rw [rasterizePolyline_cons_cons]
      apply
        (rasterizeSegment_orthogonal
          (GridSegment.mk first second)
          (octilinear _ (by
            simp [gridPolylineSegments])))
          |>.joinAtEndpoint
            (induction second octilinear.tail)
      · exact rasterizeSegment_getLast?
          (GridSegment.mk first second)
      · rw [rasterizePolyline_head?]
        rfl

/-- Positive scaling preserves the eight-direction classification of every
source segment. -/
theorem OctilinearPolyline.scale
    {points : List Cell}
    (octilinear : OctilinearPolyline points)
    {factor : Int} (factorPositive : 0 < factor) :
    OctilinearPolyline (scalePolyline factor points) := by
  intro scaledSegment scaledSegmentMember
  rw [gridPolylineSegments_scalePolyline]
    at scaledSegmentMember
  rcases List.mem_map.mp scaledSegmentMember with
    ⟨segment, segmentMember, rfl⟩
  have sourceValid :=
    octilinear segment segmentMember
  simp only [GridSegment.scale]
  have vectorEquality :
      Cell.sub
          (Cell.scale factor segment.finish)
          (Cell.scale factor segment.start) =
        Cell.scale factor
          (Cell.sub segment.finish segment.start) := by
    apply Prod.ext <;>
      simp [Cell.sub, Cell.scale] <;>
      ring
  rw [vectorEquality,
    terminalPort_scale factorPositive]
  exact sourceValid

/-! ## Incidence-route families -/

/-- Uniformly scale and then rasterize every route in an incidence family. -/
def rasterizeIncidenceRoutes
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    rasterizePolyline
      (scalePolyline factor
        (routes clauseIndex literalIndex))

@[simp]
theorem rasterizeIncidenceRoutes_apply
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) :
    rasterizeIncidenceRoutes factor routes
        clauseIndex literalIndex =
      rasterizePolyline
        (scalePolyline factor
          (routes clauseIndex literalIndex)) := rfl

/-- Scaling and rasterization carry a source endpoint to its uniformly
scaled position. -/
theorem rasterizeIncidenceRoutes_head?
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    {source : Cell}
    (routeHead :
      (routes clauseIndex literalIndex).head? =
        some source) :
    (rasterizeIncidenceRoutes factor routes
      clauseIndex literalIndex).head? =
        some (Cell.scale factor source) := by
  simp [rasterizeIncidenceRoutes, scalePolyline,
    routeHead]

/-- Scaling and rasterization carry a target endpoint to its uniformly
scaled position. -/
theorem rasterizeIncidenceRoutes_getLast?
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    {target : Cell}
    (routeLast :
      (routes clauseIndex literalIndex).getLast? =
        some target) :
    (rasterizeIncidenceRoutes factor routes
      clauseIndex literalIndex).getLast? =
        some (Cell.scale factor target) := by
  simp [rasterizeIncidenceRoutes, scalePolyline,
    routeLast]

/-- Every octilinear source route becomes orthogonal after positive uniform
refinement and rasterization. -/
theorem rasterizeIncidenceRoutes_orthogonal
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (octilinear :
      OctilinearPolyline
        (routes clauseIndex literalIndex)) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizeIncidenceRoutes factor routes
        clauseIndex literalIndex) := by
  apply rasterizePolyline_orthogonal
  apply octilinear.scale
  exact_mod_cast factorPositive

end PeriodicEightOccurrenceSplit
end LeanTrominoes
