/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedRayRasterization
import LeanTrominoes.PeriodicGridDrawingPointBounds

/-!
# Corridor bounds for retained-ray rasterization

Every retained-ray staircase is built from a fixed finite step pattern.
Between two consecutive returns to the original ray, its listed points stay
within a fixed coordinate radius of the return point.  This file makes that
uniform bound explicit: radius nine works for all eight compass rays and all
three routed-clause rays, independently of the ray length.

The resulting checkpoint certificate is the quantitative input for proving
that sufficiently large uniform scaling preserves global planar separation.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PlanarThreeSAT

/-- Coordinatewise closed square of an integral radius around a center. -/
def WithinCoordinateRadius
    (radius : Nat) (center point : Cell) : Prop :=
  (point.1 - center.1).natAbs ≤ radius ∧
    (point.2 - center.2).natAbs ≤ radius

instance (radius : Nat) (center point : Cell) :
    Decidable (WithinCoordinateRadius radius center point) := by
  unfold WithinCoordinateRadius
  infer_instance

/-- Every center lies in its own coordinate-radius square. -/
theorem withinCoordinateRadius_refl
    (radius : Nat) (center : Cell) :
    WithinCoordinateRadius radius center center := by
  simp [WithinCoordinateRadius]

/-- Translating both points preserves coordinate-radius containment. -/
theorem WithinCoordinateRadius.translate
    {radius : Nat} {center point : Cell}
    (bounded : WithinCoordinateRadius radius center point)
    (offset : Cell) :
    WithinCoordinateRadius radius
      (Cell.add offset center) (Cell.add offset point) := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simpa [WithinCoordinateRadius, Cell.add] using bounded

/-- A diagonal staircase point is within radius nine of one of its exact
returns to the source diagonal. -/
theorem diagonalStaircase_point_near_checkpoint
    (horizontal vertical : Int)
    (horizontalBound : horizontal.natAbs ≤ 9)
    (length : Nat) (start : Cell)
    {point : Cell}
    (pointMember :
      point ∈
        diagonalStaircase horizontal vertical length start) :
    ∃ index : Nat, index ≤ length ∧
      WithinCoordinateRadius 9
        (Cell.add start
          (Cell.scale index (horizontal, vertical)))
        point := by
  induction length generalizing start point with
  | zero =>
      simp only [diagonalStaircase,
        List.mem_singleton] at pointMember
      subst point
      exact
        ⟨0, by omega, by
          simpa [Cell.add, Cell.scale] using
            withinCoordinateRadius_refl 9 start⟩
  | succ length induction =>
      simp only [diagonalStaircase,
        List.mem_cons] at pointMember
      rcases pointMember with
        pointEqual | pointEqual | pointMember
      · subst point
        exact
          ⟨0, by omega, by
            simpa [Cell.add, Cell.scale] using
              withinCoordinateRadius_refl 9 start⟩
      · subst point
        refine ⟨0, by omega, ?_⟩
        rcases start with ⟨startX, startY⟩
        simpa [WithinCoordinateRadius,
          Cell.add, Cell.scale] using
            And.intro horizontalBound
              (show (0 : Int).natAbs ≤ 9 by decide)
      · rcases
          induction
            (Cell.add start (horizontal, vertical))
            pointMember with
          ⟨index, indexBound, bounded⟩
        refine ⟨index + 1, by omega, ?_⟩
        have checkpointEqual :
            Cell.add
                (Cell.add start (horizontal, vertical))
                (Cell.scale index (horizontal, vertical)) =
              Cell.add start
                (Cell.scale (↑(index + 1) : Int)
                  (horizontal, vertical)) := by
          apply Prod.ext <;>
            simp [Cell.add, Cell.scale] <;>
            ring
        rw [← checkpointEqual]
        exact bounded

/-- Every offset in one routed-clause block lies within radius nine of the
block's return point. -/
theorem routedClauseRayOffsets_within_radius
    (arm : DuplicatorArm) :
    ∀ point ∈ routedClauseRayOffsets arm,
      WithinCoordinateRadius 9 (0, 0) point := by
  cases arm <;> native_decide

/-- Translating a routed-clause block translates its radius-nine bound. -/
theorem routedClauseRayBlock_within_radius
    (arm : DuplicatorArm) (start : Cell) :
    ∀ point ∈ routedClauseRayBlock arm start,
      WithinCoordinateRadius 9 start point := by
  intro point pointMember
  rw [routedClauseRayBlock, List.mem_map] at pointMember
  rcases pointMember with
    ⟨offset, offsetMember, rfl⟩
  have bounded :=
    (routedClauseRayOffsets_within_radius arm)
      offset offsetMember
  have translated := bounded.translate start
  simpa [Cell.add] using translated

/-- Every repeated routed-clause staircase point stays within radius nine of
one of the block endpoints on the original source ray. -/
theorem routedClauseRay_point_near_checkpoint
    (arm : DuplicatorArm) (length : Nat) (start : Cell)
    {point : Cell}
    (pointMember :
      point ∈ routedClauseRay arm length start) :
    ∃ index : Nat, index ≤ length ∧
      WithinCoordinateRadius 9
        (Cell.add start
          (Cell.scale index
            (routedClauseRayPrimitive arm)))
        point := by
  induction length generalizing start point with
  | zero =>
      simp only [routedClauseRay,
        List.mem_singleton] at pointMember
      subst point
      exact
        ⟨0, by omega, by
          simpa [Cell.add, Cell.scale] using
            withinCoordinateRadius_refl 9 start⟩
  | succ length induction =>
      rw [routedClauseRay] at pointMember
      rcases mem_joinAtEndpoint pointMember with
        blockMember | trailingMember
      · exact
          ⟨0, by omega, by
            simpa [Cell.add, Cell.scale] using
              routedClauseRayBlock_within_radius
                arm start point blockMember⟩
      · rcases
          induction
            (Cell.add start
              (routedClauseRayPrimitive arm))
            trailingMember with
          ⟨index, indexBound, bounded⟩
        refine ⟨index + 1, by omega, ?_⟩
        have checkpointEqual :
            Cell.add
                (Cell.add start
                  (routedClauseRayPrimitive arm))
                (Cell.scale index
                  (routedClauseRayPrimitive arm)) =
              Cell.add start
                (Cell.scale (↑(index + 1) : Int)
                  (routedClauseRayPrimitive arm)) := by
          apply Prod.ext <;>
            simp [Cell.add, Cell.scale] <;>
            ring
        rw [← checkpointEqual]
        exact bounded

/-- A direct ray has no deviation from either of its two checkpoints. -/
theorem directRay_point_near_checkpoint
    (direction : Cell) (length : Nat) (start : Cell)
    {point : Cell}
    (pointMember :
      point ∈
        [start,
          Cell.add start (Cell.scale length direction)]) :
    ∃ index : Nat, index ≤ length ∧
      WithinCoordinateRadius 9
        (Cell.add start
          (Cell.scale index direction))
        point := by
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at pointMember
  rcases pointMember with pointEqual | pointEqual
  · subst point
    exact
      ⟨0, by omega, by
        simpa [Cell.add, Cell.scale] using
          withinCoordinateRadius_refl 9 start⟩
  · subst point
    exact
      ⟨length, le_rfl,
        withinCoordinateRadius_refl 9
          (Cell.add start
            (Cell.scale length direction))⟩

/-- Every compass-ray staircase point stays within radius nine of a
checkpoint on its source ray. -/
theorem compassRay_point_near_checkpoint
    (port : Port) (length : Nat) (start : Cell)
    {point : Cell}
    (pointMember :
      point ∈ compassRay port length start) :
    ∃ index : Nat, index ≤ length ∧
      WithinCoordinateRadius 9
        (Cell.add start
          (Cell.scale index port.unitVector))
        point := by
  cases length with
  | zero =>
      simp only [compassRay,
        List.mem_singleton] at pointMember
      subst point
      exact
        ⟨0, by omega, by
          simpa [Cell.add, Cell.scale] using
            withinCoordinateRadius_refl 9 start⟩
  | succ length =>
      cases port with
      | northwest =>
          exact
            diagonalStaircase_point_near_checkpoint
              (-1) (-1) (by decide) (length + 1)
              start pointMember
      | north =>
          exact
            directRay_point_near_checkpoint
              (0, -1) (length + 1) start
              (by simpa [compassRay,
                OccurrenceSplitRing.Port.unitVector]
                using pointMember)
      | northeast =>
          exact
            diagonalStaircase_point_near_checkpoint
              1 (-1) (by decide) (length + 1)
              start pointMember
      | east =>
          exact
            directRay_point_near_checkpoint
              (1, 0) (length + 1) start
              (by simpa [compassRay,
                OccurrenceSplitRing.Port.unitVector]
                using pointMember)
      | southeast =>
          exact
            diagonalStaircase_point_near_checkpoint
              1 1 (by decide) (length + 1)
              start pointMember
      | south =>
          exact
            directRay_point_near_checkpoint
              (0, 1) (length + 1) start
              (by simpa [compassRay,
                OccurrenceSplitRing.Port.unitVector]
                using pointMember)
      | southwest =>
          exact
            diagonalStaircase_point_near_checkpoint
              (-1) 1 (by decide) (length + 1)
              start pointMember
      | west =>
          exact
            directRay_point_near_checkpoint
              (-1, 0) (length + 1) start
              (by simpa [compassRay,
                OccurrenceSplitRing.Port.unitVector]
                using pointMember)

/-- Primitive direction of a retained ray, independent of its length. -/
def RetainedRay.primitive : RetainedRay → Cell
  | .compass port _ => port.unitVector
  | .routedClause arm _ => routedClauseRayPrimitive arm

/-- Number of primitive blocks in a retained ray. -/
def RetainedRay.length : RetainedRay → Nat
  | .compass _ length => length
  | .routedClause _ length => length

/-- A retained ray's displacement is its length times its primitive
direction. -/
@[simp]
theorem RetainedRay.vector_eq_scale_length_primitive
    (ray : RetainedRay) :
    ray.vector =
      Cell.scale ray.length ray.primitive := by
  cases ray <;>
    rfl

/-- The uniform radius-nine checkpoint certificate for either retained ray
family. -/
theorem RetainedRay.rasterize_point_near_checkpoint
    (ray : RetainedRay) (start : Cell)
    {point : Cell}
    (pointMember : point ∈ ray.rasterize start) :
    ∃ index : Nat, index ≤ ray.length ∧
      WithinCoordinateRadius 9
        (Cell.add start
          (Cell.scale index ray.primitive))
        point := by
  cases ray with
  | compass port length =>
      exact
        compassRay_point_near_checkpoint
          port length start pointMember
  | routedClause arm length =>
      exact
        routedClauseRay_point_near_checkpoint
          arm length start pointMember

/-- A point lies in the uniform rasterization corridor of a retained
segment when it is near a primitive checkpoint between the segment's
endpoints. -/
def InRetainedSegmentRasterCorridor
    (segment : GridSegment) (point : Cell) : Prop :=
  ∃ primitive : Cell, ∃ length index : Nat,
    0 < length ∧
      Cell.sub segment.finish segment.start =
        Cell.scale length primitive ∧
      index ≤ length ∧
      WithinCoordinateRadius 9
        (Cell.add segment.start
          (Cell.scale index primitive))
        point

/-- Every listed point introduced while rasterizing one supported segment
lies in its uniform checkpoint corridor. -/
theorem rasterizeRetainedSegment_point_in_corridor
    (segment : GridSegment)
    (retained :
      RetainedRayVector
        (Cell.sub segment.finish segment.start))
    {point : Cell}
    (pointMember :
      point ∈ rasterizeRetainedSegment segment) :
    InRetainedSegmentRasterCorridor segment point := by
  unfold RetainedRayVector at retained
  unfold rasterizeRetainedSegment at pointMember
  generalize classified :
    retainedRayClassify
        (Cell.sub segment.finish segment.start) =
      classifiedRay at retained pointMember
  cases classifiedRay with
  | none =>
      simp at retained
  | some ray =>
      have sound :=
        retainedRayClassify_sound classified
      rcases
          ray.rasterize_point_near_checkpoint
            segment.start pointMember with
        ⟨index, indexBound, bounded⟩
      exact
        ⟨ray.primitive, ray.length, index,
          sound.1,
          sound.2.trans
            ray.vector_eq_scale_length_primitive,
          indexBound, bounded⟩

/-- Every point of a rasterized nondegenerate retained polyline belongs to
the checkpoint corridor of some source segment. -/
theorem rasterizeRetainedPolyline_point_in_corridor
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    (length : 2 ≤ points.length)
    {point : Cell}
    (pointMember :
      point ∈ rasterizeRetainedPolyline points) :
    ∃ segment ∈ gridPolylineSegments points,
      InRetainedSegmentRasterCorridor segment point := by
  induction points using List.twoStepInduction with
  | nil =>
      simp at length
  | singleton only =>
      simp at length
  | cons_cons first second rest _ tailInduction =>
      rw [rasterizeRetainedPolyline_cons_cons,
        joinAtEndpoint, List.mem_append] at pointMember
      rcases pointMember with
        firstSegmentMember | tailMember
      · let segment : GridSegment :=
          GridSegment.mk first second
        have segmentMember :
            segment ∈
              gridPolylineSegments
                (first :: second :: rest) := by
          simp [segment, gridPolylineSegments]
        exact
          ⟨segment, segmentMember,
            rasterizeRetainedSegment_point_in_corridor
              segment
              (retained segment segmentMember)
              firstSegmentMember⟩
      · cases rest with
        | nil =>
            simp at tailMember
        | cons third rest =>
            have tailPointMember :
                point ∈
                  rasterizeRetainedPolyline
                    (second :: third :: rest) :=
              List.mem_of_mem_tail tailMember
            rcases
                tailInduction second retained.tail
                  (by simp) tailPointMember with
              ⟨segment, segmentMember, bounded⟩
            exact
              ⟨segment, by
                exact
                  List.mem_cons_of_mem
                    (GridSegment.mk first second)
                    segmentMember,
                bounded⟩

/-- The same corridor provenance for a positively scaled and rasterized
incidence route. -/
theorem rasterizeRetainedIncidenceRoutes_point_in_corridor
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat)
    (retained :
      RetainedRayPolyline
        (routes clauseIndex literalIndex))
    (length :
      2 ≤ (routes clauseIndex literalIndex).length)
    {point : Cell}
    (pointMember :
      point ∈
        rasterizeRetainedIncidenceRoutes factor routes
          clauseIndex literalIndex) :
    ∃ segment ∈
        gridPolylineSegments
          (scalePolyline factor
            (routes clauseIndex literalIndex)),
      InRetainedSegmentRasterCorridor segment point := by
  apply rasterizeRetainedPolyline_point_in_corridor
    (retained.scale factorPositive)
  · simpa [scalePolyline] using length
  · exact pointMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
