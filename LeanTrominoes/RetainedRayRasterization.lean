/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RoutedClauseRayStaircase

/-!
# Rasterizing every retained planar-SAT ray

Most retained planar-SAT route segments lie on the eight compass rays.  The
direct routed-clause star contributes three additional primitive slopes.
This file combines both cases into one executable classifier and lifts their
unit-step rasterizations from segments to polylines.

The resulting predicate is intentionally geometric rather than tied to a
particular source-gadget tag.  Later files can prove that each retained local
route satisfies it, then uniformly scale and rasterize the assembled route
family.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- A classified ray supported by the retained planar-SAT construction. -/
inductive RetainedRay where
  | compass (port : Port) (length : Nat)
  | routedClause (arm : DuplicatorArm) (length : Nat)
  deriving DecidableEq, Repr

/-- The displacement represented by a retained-ray classification. -/
def RetainedRay.vector : RetainedRay → Cell
  | .compass port length =>
      Cell.scale length port.unitVector
  | .routedClause arm length =>
      Cell.scale length
        (routedClauseRayPrimitive arm)

/-- Replace a classified ray by its orthogonal staircase. -/
def RetainedRay.rasterize
    (ray : RetainedRay) (start : Cell) : List Cell :=
  match ray with
  | .compass port length =>
      compassRay port length start
  | .routedClause arm length =>
      routedClauseRay arm length start

@[simp]
theorem RetainedRay.rasterize_head?
    (ray : RetainedRay) (start : Cell) :
    (ray.rasterize start).head? = some start := by
  cases ray <;> simp [RetainedRay.rasterize]

@[simp]
theorem RetainedRay.rasterize_getLast?
    (ray : RetainedRay) (start : Cell) :
    (ray.rasterize start).getLast? =
      some (Cell.add start ray.vector) := by
  cases ray <;>
    simp [RetainedRay.rasterize,
      RetainedRay.vector]

/-- Both retained ray families rasterize to orthogonal polylines. -/
theorem RetainedRay.rasterize_orthogonal
    (ray : RetainedRay) (start : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (ray.rasterize start) := by
  cases ray with
  | compass port length =>
      exact compassRay_orthogonal port length start
  | routedClause arm length =>
      exact routedClauseRay_orthogonal arm length start

/-- Classify either a compass ray or one of the three exceptional
routed-clause rays. -/
def retainedRayClassify (vector : Cell) :
    Option RetainedRay :=
  match terminalPort vector with
  | some port =>
      some
        (.compass port
          (compassLength port vector))
  | none =>
      match routedClauseRayClassify vector with
      | some (arm, length) =>
          some (.routedClause arm length)
      | none => none

/-- A successful retained-ray classification has positive length and
represents exactly the input displacement. -/
theorem retainedRayClassify_sound
    {vector : Cell} {ray : RetainedRay}
    (classified :
      retainedRayClassify vector = some ray) :
    0 < (match ray with
      | .compass _ length => length
      | .routedClause _ length => length) ∧
      vector = ray.vector := by
  unfold retainedRayClassify at classified
  generalize terminalClassification :
    terminalPort vector = classifiedPort
  cases classifiedPort with
  | some port =>
      simp [terminalClassification] at classified
      subst ray
      simpa [RetainedRay.vector] using
        compassLength_pos_and_scale
          terminalClassification
  | none =>
      generalize routedClassification :
        routedClauseRayClassify vector =
          classifiedRoutedRay
      cases classifiedRoutedRay with
      | none =>
          simp [terminalClassification,
            routedClassification] at classified
      | some armLength =>
          rcases armLength with ⟨arm, length⟩
          simp [terminalClassification,
            routedClassification] at classified
          subst ray
          simpa [RetainedRay.vector] using
            routedClauseRayClassify_sound
              routedClassification

/-- A displacement is rasterizable precisely when the combined executable
classifier succeeds. -/
def RetainedRayVector (vector : Cell) : Prop :=
  (retainedRayClassify vector).isSome

instance (vector : Cell) :
    Decidable (RetainedRayVector vector) := by
  unfold RetainedRayVector
  infer_instance

/-- Every compass-ray displacement is a retained-ray displacement. -/
theorem RetainedRayVector.of_octilinear
    {vector : Cell}
    (octilinear : (terminalPort vector).isSome) :
    RetainedRayVector vector := by
  unfold RetainedRayVector retainedRayClassify
  generalize classified :
    terminalPort vector = classifiedPort
  cases classifiedPort with
  | none =>
      simp [classified] at octilinear
  | some port =>
      simp

/-- Positive integral scaling preserves the retained-ray class. -/
theorem RetainedRayVector.scale
    {vector : Cell}
    (retained : RetainedRayVector vector)
    {factor : Nat} (factorPositive : 0 < factor) :
    RetainedRayVector
      (Cell.scale factor vector) := by
  unfold RetainedRayVector at retained ⊢
  unfold retainedRayClassify at retained ⊢
  generalize terminalClassification :
    terminalPort vector = classifiedPort
  cases classifiedPort with
  | some port =>
      have scaledTerminal :
          terminalPort (Cell.scale factor vector) =
            some port := by
        rw [terminalPort_scale
          (by exact_mod_cast factorPositive),
          terminalClassification]
      simp [scaledTerminal]
  | none =>
      generalize routedClassification :
        routedClauseRayClassify vector =
          classifiedRoutedRay
      cases classifiedRoutedRay with
      | none =>
          simp [terminalClassification,
            routedClassification] at retained
      | some armLength =>
          rcases armLength with ⟨arm, length⟩
          have source :=
            routedClauseRayClassify_sound
              routedClassification
          have productPositive :
              0 < factor * length :=
            Nat.mul_pos factorPositive source.1
          have scaledRouted :
              routedClauseRayClassify
                  (Cell.scale factor vector) =
                some (arm, factor * length) := by
            rw [source.2, Cell.scale_scale]
            simpa only [Nat.cast_mul] using
              routedClauseRayClassify_scale
                arm productPositive
          have scaledTerminal :
              terminalPort
                  (Cell.scale factor vector) =
                none := by
            rw [terminalPort_scale
              (by exact_mod_cast factorPositive),
              terminalClassification]
          simp [scaledTerminal, scaledRouted]

/-- Rasterize one segment whenever possible, retaining a direct fallback so
the operation remains total. -/
def rasterizeRetainedSegment
    (segment : GridSegment) : List Cell :=
  match
      retainedRayClassify
        (Cell.sub segment.finish segment.start) with
  | some ray => ray.rasterize segment.start
  | none => [segment.start, segment.finish]

@[simp]
theorem rasterizeRetainedSegment_head?
    (segment : GridSegment) :
    (rasterizeRetainedSegment segment).head? =
      some segment.start := by
  unfold rasterizeRetainedSegment
  generalize classified :
    retainedRayClassify
      (Cell.sub segment.finish segment.start) =
        classifiedRay
  cases classifiedRay <;> simp

@[simp]
theorem rasterizeRetainedSegment_getLast?
    (segment : GridSegment) :
    (rasterizeRetainedSegment segment).getLast? =
      some segment.finish := by
  unfold rasterizeRetainedSegment
  generalize classified :
    retainedRayClassify
      (Cell.sub segment.finish segment.start) =
        classifiedRay
  cases classifiedRay with
  | none =>
      simp
  | some ray =>
      rw [RetainedRay.rasterize_getLast?]
      have exactVector :=
        (retainedRayClassify_sound classified).2
      apply congrArg some
      rw [← exactVector]
      apply Prod.ext <;>
        simp [Cell.add, Cell.sub]

/-- Every classified retained segment rasterizes orthogonally. -/
theorem rasterizeRetainedSegment_orthogonal
    (segment : GridSegment)
    (retained :
      RetainedRayVector
        (Cell.sub segment.finish segment.start)) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizeRetainedSegment segment) := by
  unfold RetainedRayVector at retained
  unfold rasterizeRetainedSegment
  generalize classified :
    retainedRayClassify
      (Cell.sub segment.finish segment.start) =
        classifiedRay
  cases classifiedRay with
  | none =>
      simp [classified] at retained
  | some ray =>
      exact ray.rasterize_orthogonal segment.start

/-- Every nondegenerate segment of a polyline is a supported retained ray. -/
def RetainedRayPolyline (points : List Cell) : Prop :=
  ∀ segment ∈ gridPolylineSegments points,
    RetainedRayVector
      (Cell.sub segment.finish segment.start)

instance (points : List Cell) :
    Decidable (RetainedRayPolyline points) := by
  unfold RetainedRayPolyline
  infer_instance

/-- Every octilinear polyline is a retained-ray polyline. -/
theorem RetainedRayPolyline.of_octilinear
    {points : List Cell}
    (octilinear : OctilinearPolyline points) :
    RetainedRayPolyline points := by
  intro segment segmentMember
  exact RetainedRayVector.of_octilinear
    (octilinear segment segmentMember)

/-- Replace every retained-ray segment independently and join the results at
their shared source vertices. -/
def rasterizeRetainedPolyline : List Cell → List Cell
  | [] => []
  | first :: rest =>
      match rest with
      | [] => [first]
      | second :: _tail =>
          joinAtEndpoint
            (rasterizeRetainedSegment
              (GridSegment.mk first second))
            (rasterizeRetainedPolyline rest)

@[simp]
theorem rasterizeRetainedPolyline_nil :
    rasterizeRetainedPolyline [] = [] := by
  rw [rasterizeRetainedPolyline]

@[simp]
theorem rasterizeRetainedPolyline_singleton
    (point : Cell) :
    rasterizeRetainedPolyline [point] = [point] := by
  rw [rasterizeRetainedPolyline]

@[simp]
theorem rasterizeRetainedPolyline_cons_cons
    (first second : Cell) (rest : List Cell) :
    rasterizeRetainedPolyline
        (first :: second :: rest) =
      joinAtEndpoint
        (rasterizeRetainedSegment
          (GridSegment.mk first second))
        (rasterizeRetainedPolyline
          (second :: rest)) := by
  rfl

@[simp]
theorem rasterizeRetainedPolyline_head?
    (points : List Cell) :
    (rasterizeRetainedPolyline points).head? =
      points.head? := by
  induction points using List.twoStepInduction with
  | nil =>
      simp
  | singleton point =>
      simp
  | cons_cons first second rest _ induction =>
      rw [rasterizeRetainedPolyline_cons_cons]
      simpa using
        joinAtEndpoint_head?
          (rasterizeRetainedSegment_head?
            (GridSegment.mk first second))

@[simp]
theorem rasterizeRetainedPolyline_getLast?
    (points : List Cell) :
    (rasterizeRetainedPolyline points).getLast? =
      points.getLast? := by
  induction points using List.twoStepInduction with
  | nil =>
      simp
  | singleton point =>
      simp
  | cons_cons first second rest _ induction =>
      rw [rasterizeRetainedPolyline_cons_cons]
      let target :=
        (second :: rest).getLast (by simp)
      have sourceLast :
          (second :: rest).getLast? =
            some target := by
        rw [List.getLast?_eq_some_getLast]
      have rasterizedLast :
          (rasterizeRetainedPolyline
            (second :: rest)).getLast? =
              some target := by
        rw [induction second, sourceLast]
      have joinedLast :=
        joinAtEndpoint_getLast?
          (rasterizeRetainedSegment_getLast?
            (GridSegment.mk first second))
          (by
            rw [rasterizeRetainedPolyline_head?]
            rfl)
          rasterizedLast
      rw [joinedLast, List.getLast?_cons_cons,
        sourceLast]

/-- Removing the first point preserves retained-ray rasterizability. -/
theorem RetainedRayPolyline.tail
    {points : List Cell}
    (retained : RetainedRayPolyline points) :
    RetainedRayPolyline points.tail := by
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
          exact retained segment
            (List.mem_cons_of_mem _ segmentMember)

/-- Rasterizing a retained-ray polyline yields one orthogonal polyline. -/
theorem rasterizeRetainedPolyline_orthogonal
    {points : List Cell}
    (retained : RetainedRayPolyline points) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizeRetainedPolyline points) := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | singleton point =>
      simp [PeriodicOrthocrossing.OrthogonalPolyline]
  | cons_cons first second rest _ induction =>
      rw [rasterizeRetainedPolyline_cons_cons]
      apply
        (rasterizeRetainedSegment_orthogonal
          (GridSegment.mk first second)
          (retained _ (by
            simp [gridPolylineSegments])))
          |>.joinAtEndpoint
            (induction second retained.tail)
      · exact rasterizeRetainedSegment_getLast?
          (GridSegment.mk first second)
      · rw [rasterizeRetainedPolyline_head?]
        rfl

/-- Positive uniform scaling preserves every retained-ray segment. -/
theorem RetainedRayPolyline.scale
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    {factor : Nat} (factorPositive : 0 < factor) :
    RetainedRayPolyline
      (scalePolyline factor points) := by
  intro scaledSegment scaledSegmentMember
  rw [gridPolylineSegments_scalePolyline]
    at scaledSegmentMember
  rcases List.mem_map.mp scaledSegmentMember with
    ⟨segment, segmentMember, rfl⟩
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
  rw [vectorEquality]
  exact
    (retained segment segmentMember).scale
      factorPositive

/-! ## Incidence-route families -/

/-- Uniformly scale and then retained-ray-rasterize every route in an
incidence family. -/
def rasterizeRetainedIncidenceRoutes
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  fun clauseIndex literalIndex =>
    rasterizeRetainedPolyline
      (scalePolyline factor
        (routes clauseIndex literalIndex))

@[simp]
theorem rasterizeRetainedIncidenceRoutes_apply
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) :
    rasterizeRetainedIncidenceRoutes factor routes
        clauseIndex literalIndex =
      rasterizeRetainedPolyline
        (scalePolyline factor
          (routes clauseIndex literalIndex)) := rfl

/-- Retained-ray rasterization preserves a route's scaled source endpoint. -/
theorem rasterizeRetainedIncidenceRoutes_head?
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    {source : Cell}
    (routeHead :
      (routes clauseIndex literalIndex).head? =
        some source) :
    (rasterizeRetainedIncidenceRoutes factor routes
      clauseIndex literalIndex).head? =
        some (Cell.scale factor source) := by
  simp [rasterizeRetainedIncidenceRoutes,
    scalePolyline, routeHead]

/-- Retained-ray rasterization preserves a route's scaled target endpoint. -/
theorem rasterizeRetainedIncidenceRoutes_getLast?
    (factor : Nat)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    {target : Cell}
    (routeLast :
      (routes clauseIndex literalIndex).getLast? =
        some target) :
    (rasterizeRetainedIncidenceRoutes factor routes
      clauseIndex literalIndex).getLast? =
        some (Cell.scale factor target) := by
  simp [rasterizeRetainedIncidenceRoutes,
    scalePolyline, routeLast]

/-- A retained source route becomes orthogonal after positive uniform
refinement and rasterization. -/
theorem rasterizeRetainedIncidenceRoutes_orthogonal
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (retained :
      RetainedRayPolyline
        (routes clauseIndex literalIndex)) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (rasterizeRetainedIncidenceRoutes factor routes
        clauseIndex literalIndex) := by
  apply rasterizeRetainedPolyline_orthogonal
  exact retained.scale factorPositive

end PeriodicEightOccurrenceSplit
end LeanTrominoes
