import LeanTrominoes.PeriodicThreeDMVertexNormalizationLocalTemplateSeparation
import LeanTrominoes.OrthogonalPolylineRefinementStrictSeparation

/-!
# Separation of trimmed normalization corridors

The middle piece of a normalized route is a contiguous slice of the
twelvefold unit subdivision of the old route, with three points removed at
both ends.  This module proves the generic slice lemmas needed to inherit
strict separation between such middles.  It also proves separation from a
local template whenever the template center is not an endpoint of the old
route; the remaining incident-endpoint case is finite directional geometry.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open DegreeThreeVertexNormalization

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every segment remaining after dropping an initial prefix was already a
segment of the original polyline. -/
theorem gridPolylineSegments_drop_subset
    (count : Nat) (points : List Cell) :
    ∀ ⦃segment⦄,
      segment ∈ gridPolylineSegments (points.drop count) →
        segment ∈ gridPolylineSegments points := by
  induction count generalizing points with
  | zero => simp
  | succ count induction =>
      cases points with
      | nil => simp [gridPolylineSegments]
      | cons first rest =>
          intro segment member
          change segment ∈
            gridPolylineSegments (rest.drop count) at member
          apply gridPolylineSegments_tail_subset (first :: rest)
          exact induction rest member

/-- Every segment of an initial prefix was already a segment of the
original polyline. -/
theorem gridPolylineSegments_take_subset
    (count : Nat) (points : List Cell) :
    ∀ ⦃segment⦄,
      segment ∈ gridPolylineSegments (points.take count) →
        segment ∈ gridPolylineSegments points := by
  induction count generalizing points with
  | zero => simp [gridPolylineSegments]
  | succ count induction =>
      cases points with
      | nil => simp [gridPolylineSegments]
      | cons first rest =>
          cases count with
          | zero => simp [gridPolylineSegments]
          | succ count =>
              cases rest with
              | nil => simp [gridPolylineSegments]
              | cons second rest =>
                  intro segment member
                  simp only [List.take_succ_cons,
                    gridPolylineSegments, List.mem_cons] at member ⊢
                  rcases member with rfl | member
                  · exact Or.inl rfl
                  · exact Or.inr
                      (induction (second :: rest) member)

/-- Restricting the first route to a dropped suffix preserves strict
separation. -/
theorem RoutesStrictlyAvoidEachOther.drop_left
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (count : Nat) :
    RoutesStrictlyAvoidEachOther (first.drop count) second := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    exact strict.1 firstSegment
      (gridPolylineSegments_drop_subset count first firstMember)
      secondSegment secondMember
  · intro firstPoint firstMember secondSegment secondMember
    exact strict.2.1 firstPoint
      (List.mem_of_mem_drop firstMember)
      secondSegment secondMember
  · intro secondPoint secondMember firstSegment firstMember
    exact strict.2.2.1 secondPoint secondMember firstSegment
      (gridPolylineSegments_drop_subset count first firstMember)
  · intro firstPoint firstMember secondPoint secondMember
    exact strict.2.2.2 firstPoint
      (List.mem_of_mem_drop firstMember) secondPoint secondMember

/-- Restricting the first route to a taken prefix preserves strict
separation. -/
theorem RoutesStrictlyAvoidEachOther.take_left
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (count : Nat) :
    RoutesStrictlyAvoidEachOther (first.take count) second := by
  unfold RoutesStrictlyAvoidEachOther at strict ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    exact strict.1 firstSegment
      (gridPolylineSegments_take_subset count first firstMember)
      secondSegment secondMember
  · intro firstPoint firstMember secondSegment secondMember
    exact strict.2.1 firstPoint
      (List.mem_of_mem_take firstMember)
      secondSegment secondMember
  · intro secondPoint secondMember firstSegment firstMember
    exact strict.2.2.1 secondPoint secondMember firstSegment
      (gridPolylineSegments_take_subset count first firstMember)
  · intro firstPoint firstMember secondPoint secondMember
    exact strict.2.2.2 firstPoint
      (List.mem_of_mem_take firstMember) secondPoint secondMember

/-- The corresponding restriction of the second route follows by
symmetry. -/
theorem RoutesStrictlyAvoidEachOther.drop_right
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (count : Nat) :
    RoutesStrictlyAvoidEachOther first (second.drop count) :=
  (strict.symm.drop_left count).symm

/-- The corresponding taken-prefix restriction of the second route. -/
theorem RoutesStrictlyAvoidEachOther.take_right
    {first second : List Cell}
    (strict : RoutesStrictlyAvoidEachOther first second)
    (count : Nat) :
    RoutesStrictlyAvoidEachOther first (second.take count) :=
  (strict.symm.take_left count).symm

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- Every point of the symmetric three-point endpoint trim remains a point
of the original list. -/
theorem List.mem_of_mem_symmetricTrim
    {α : Type*} {items : List α} {point : α}
    (member : point ∈
      (items.drop 3).take (items.length - 6)) :
    point ∈ items :=
  List.mem_of_mem_drop (List.mem_of_mem_take member)

/-- The symmetric trim lies in the tail of its source list. -/
theorem List.mem_tail_of_mem_symmetricTrim
    {α : Type*} {items : List α} {point : α}
    (member : point ∈
      (items.drop 3).take (items.length - 6)) :
    point ∈ items.tail := by
  have dropped : point ∈ items.drop 3 :=
    List.mem_of_mem_take member
  cases items with
  | nil => simp at dropped
  | cons first rest =>
      exact List.mem_of_mem_drop (by simpa using dropped)

/-- For a sufficiently long source list, the symmetric trim also lies in
the source list with its final point removed. -/
theorem List.mem_dropLast_of_mem_symmetricTrim
    {α : Type*} {items : List α} {point : α}
    (long : 7 ≤ items.length)
    (member : point ∈
      (items.drop 3).take (items.length - 6)) :
    point ∈ items.dropLast := by
  have inShortTake :
      point ∈ items.take (3 + (items.length - 6)) := by
    rw [List.take_add]
    exact List.mem_append_right _ member
  have shortLe : 3 + (items.length - 6) ≤ items.length - 1 := by
    omega
  have takeEquation :
      items.take (3 + (items.length - 6)) =
        (items.take (items.length - 1)).take
          (3 + (items.length - 6)) := by
    rw [List.take_take, Nat.min_eq_left shortLe]
  rw [takeEquation] at inShortTake
  rw [List.dropLast_eq_take]
  exact List.mem_of_mem_take inShortTake

/-- A duplicate-free long list has no original endpoint in its symmetric
three-point trim. -/
theorem List.symmetricTrim_not_endpoint
    {items : List Cell}
    (nodup : items.Nodup)
    (long : 7 ≤ items.length)
    {point : Cell}
    (member : point ∈
      (items.drop 3).take (items.length - 6)) :
    ¬RoutePointIsEndpoint items point := by
  intro endpoint
  rcases endpoint with head | last
  · exact
      (AxisDirection.headNotInTail_of_nodup nodup
        point head)
        (List.mem_tail_of_mem_symmetricTrim member)
  · exact
      (AxisDirection.lastNotInDropLast_of_nodup nodup
        point last)
        (List.mem_dropLast_of_mem_symmetricTrim long member)

/-- Complete avoidance of two duplicate-free long routes becomes strict
after removing three points from both ends. -/
theorem symmetricTrims_strictlyAvoidEachOther
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (firstNodup : first.Nodup)
    (_secondNodup : second.Nodup)
    (firstLong : 7 ≤ first.length)
    (_secondLong : 7 ≤ second.length) :
    RoutesStrictlyAvoidEachOther
      ((first.drop 3).take (first.length - 6))
      ((second.drop 3).take (second.length - 6)) := by
  apply routesStrictlyAvoidEachOther_of_avoid_of_noContact
  · apply routesAvoidEachOther_of_mem
    · intro firstSegment firstMember secondSegment secondMember
      exact avoid.segmentsAvoid_of_mem firstSegment
        (gridPolylineSegments_drop_subset 3 first
          (gridPolylineSegments_take_subset _ _ firstMember))
        secondSegment
        (gridPolylineSegments_drop_subset 3 second
          (gridPolylineSegments_take_subset _ _ secondMember))
    · intro firstPoint firstMember secondSegment secondMember
      exact avoid.firstPointsAvoid_of_mem firstPoint
        (List.mem_of_mem_symmetricTrim firstMember)
        secondSegment
        (gridPolylineSegments_drop_subset 3 second
          (gridPolylineSegments_take_subset _ _ secondMember))
    · intro secondPoint secondMember firstSegment firstMember
      exact avoid.secondPointsAvoid_of_mem secondPoint
        (List.mem_of_mem_symmetricTrim secondMember)
        firstSegment
        (gridPolylineSegments_drop_subset 3 first
          (gridPolylineSegments_take_subset _ _ firstMember))
    · intro firstPoint firstMember secondPoint secondMember equal
      have firstSourceMember :=
        List.mem_of_mem_symmetricTrim firstMember
      have secondSourceMember :=
        List.mem_of_mem_symmetricTrim secondMember
      rcases List.mem_iff_get.mp firstSourceMember with
        ⟨firstIndex, firstAt⟩
      rcases List.mem_iff_get.mp secondSourceMember with
        ⟨secondIndex, secondAt⟩
      have endpoints := avoid.2.2.2 firstIndex secondIndex
        (firstAt.trans (equal.trans secondAt.symm))
      rw [firstAt, secondAt] at endpoints
      exact
        ((List.symmetricTrim_not_endpoint
          firstNodup firstLong firstMember) endpoints.1).elim
  · intro firstPoint firstMember secondPoint secondMember equal
    have firstSourceMember :=
      List.mem_of_mem_symmetricTrim firstMember
    have secondSourceMember :=
      List.mem_of_mem_symmetricTrim secondMember
    rcases List.mem_iff_get.mp firstSourceMember with
      ⟨firstIndex, firstAt⟩
    rcases List.mem_iff_get.mp secondSourceMember with
      ⟨secondIndex, secondAt⟩
    have endpoints := avoid.2.2.2 firstIndex secondIndex
      (firstAt.trans (equal.trans secondAt.symm))
    rw [firstAt, secondAt] at endpoints
    exact
      ((List.symmetricTrim_not_endpoint
        firstNodup firstLong firstMember) endpoints.1).elim

/-- The executable magnified route is ordered unit subdivision of the
twelvefold-scaled route followed by the common center translation. -/
theorem magnifiedUnitRoute_eq_translate_scale
    (points : List Cell) :
    magnifiedUnitRoute points =
      AxisDirection.unitSubdividePolyline
        (translatePolyline center (scalePolyline 12 points)) := by
  unfold magnifiedUnitRoute scalePolyline
    PeriodicOrthocrossing.translatePolyline
  congr 1
  conv_rhs => rw [List.map_map]
  change points.map normalizeVertexPosition =
    points.map (fun point => Cell.add center (Cell.scale 12 point))
  apply List.map_congr_left
  intro point pointMember
  rcases point with ⟨pointX, pointY⟩
  simp [normalizeVertexPosition, vertexNormalizationScale,
    center, Cell.add, Cell.scale]
  constructor <;> ring

/-- If an old orthogonal route completely avoids an old lattice point,
then its trimmed magnified corridor is strictly separated from every
Figure 2 template installed at that point. -/
theorem trimmedMagnifiedRoute_strictlyAvoids_normalizationTemplateAt_route
    {oldRoute : List Cell} {position : Cell}
    (oldOrthogonal : OrthogonalPolyline oldRoute)
    (oldPointsAvoid : ∀ point ∈ oldRoute, point ≠ position)
    (oldSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments oldRoute,
        segment.IsAxisAligned → ¬segment.Contains position)
    (omitted : VertexSide) (port : CanonicalVertexPort) :
    RoutesStrictlyAvoidEachOther
      (trimmedMagnifiedRoute oldRoute)
      (normalizationTemplateAt position (route omitted port)) := by
  have scaledStrict :=
    routesStrictlyAvoidEachOther_translateScalePolyline_pointNeighborhood
      (source := oldRoute)
      (nearby := normalizationTemplateAt position (route omitted port))
      (center := position) (offset := center)
      (factor := 12) (radius := 3)
      (by decide) (by decide)
      oldPointsAvoid oldSegmentsAvoid
      (by
        simpa [normalizeVertexPosition, vertexNormalizationScale,
          Cell.add, add_comm] using
          normalizationTemplateAt_route_withinCoordinateRadius
            position omitted port)
  have scaledOrthogonal :
      OrthogonalPolyline
        (translatePolyline center (scalePolyline 12 oldRoute)) :=
    (oldOrthogonal.scalePolyline (by decide)).translate center
  have templateOrthogonal :
      OrthogonalPolyline
        (normalizationTemplateAt position (route omitted port)) := by
    have localOrthogonal :
        OrthogonalPolyline (route omitted port) :=
      (route_unitSteps omitted port).imp
        (fun _ _ step => step.isAxisAligned)
    unfold normalizationTemplateAt
    exact localOrthogonal.translate _
  have refinedStrict :
      RoutesStrictlyAvoidEachOther
        (magnifiedUnitRoute oldRoute)
        (normalizationTemplateAt position (route omitted port)) := by
    rw [magnifiedUnitRoute_eq_translate_scale]
    exact scaledStrict.refine_left
      scaledOrthogonal templateOrthogonal
      (AxisDirection.unitSubdividePolyline_refines scaledOrthogonal)
  exact
    (refinedStrict.drop_left 3).take_left
      ((magnifiedUnitRoute oldRoute).length - 6)

end PeriodicThreeDM
end LeanTrominoes
