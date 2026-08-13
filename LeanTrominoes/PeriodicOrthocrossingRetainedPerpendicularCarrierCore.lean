/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingPerpendicularCarrierGeometry

/-!
# Core geometry of selected retained perpendicular carriers

Zero-shift ownership makes a selected link's first boundary canonical; a
first terminal is already in the legacy neighboring window.  Hence every
selected link starts on a neighboring source occurrence, and perpendicular
selected links necessarily use different occurrence keys.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The first node of a selected retained link is also in the canonical
neighbor-window carrier enumeration. -/
theorem retainedDrawingCompleteCarrierLink_first_mem_drawingCarrierNodes
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    link.first ∈ drawingCarrierNodes graph := by
  have retainedFirst :=
    (retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem).1
  have representative :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).2
  cases firstNode : link.first with
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at retainedFirst
        rw [firstNode] at retainedFirst
        rcases List.mem_append.mp retainedFirst with
          terminalMem | boundaryMem
        · simpa using terminalMem
        · simp at boundaryMem
      unfold drawingCarrierNodes
      exact List.mem_append_left _
        (List.mem_map.mpr ⟨terminal, terminalMem, rfl⟩)
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at retainedFirst
        rw [firstNode] at retainedFirst
        rcases List.mem_append.mp retainedFirst with
          terminalMem | boundaryMem
        · simp at terminalMem
        · simpa using boundaryMem
      have normalizedMem :=
        retainedCrossingBoundary_periodNormalize_mem
          graph boundaryMem
      have normalizedSelf :=
        carrierLinkRepresentative_first_boundary_normalizes_self
          graph firstNode representative
      rw [normalizedSelf] at normalizedMem
      unfold drawingCarrierNodes
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨boundary, normalizedMem, rfl⟩)

/-- Every selected retained link starts on a neighboring translated source
occurrence. -/
theorem retainedDrawingCompleteCarrierLink_first_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph) :
    IsNeighborTranslation link.first.translate :=
  carrierNode_translate_neighbor graph
    (retainedDrawingCompleteCarrierLink_first_mem_drawingCarrierNodes
      linkMem)

/-- Perpendicular selected retained links have different physical occurrence
keys. -/
theorem retainedDrawingCompleteCarrierLinks_keys_ne_of_perpendicular
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks graph)
    (perpendicular :
      CarrierLinksPerpendicular firstLink secondLink) :
    firstLink.first.carrierKey ≠
      secondLink.first.carrierKey := by
  intro keyEqual
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have supportEqual :=
    retainedCarrierNode_supportingSegment_eq_of_carrierKey_eq
      firstEndpoints.1 secondEndpoints.1 keyEqual
  have firstAligned :
      firstLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      firstLink.first.indexed
      (retainedCarrierNode_indexed_mem graph firstEndpoints.1)
  have secondAligned :
      secondLink.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      secondLink.first.indexed
      (retainedCarrierNode_indexed_mem graph secondEndpoints.1)
  rcases perpendicular with
      ⟨firstHorizontalTag, secondVerticalTag⟩ |
      ⟨firstVerticalTag, secondHorizontalTag⟩
  · have firstHorizontal :
        (firstLink.first.supportingSegment graph).IsHorizontal := by
      exact
        (GridSegment.isHorizontal_translate _ _).mpr
          ((retainedCarrierNode_isHorizontal_iff
            graph firstEndpoints.1 firstAligned).mp
              firstHorizontalTag)
    have secondVertical :
        (secondLink.first.supportingSegment graph).IsVertical := by
      apply (GridSegment.isVertical_translate _ _).mpr
      exact secondAligned.resolve_left fun secondHorizontal =>
        secondVerticalTag
          ((retainedCarrierNode_isHorizontal_iff
            graph secondEndpoints.1 secondAligned).mpr
              secondHorizontal)
    rw [supportEqual] at firstHorizontal
    exact secondVertical.2 firstHorizontal.1
  · have firstVertical :
        (firstLink.first.supportingSegment graph).IsVertical := by
      apply (GridSegment.isVertical_translate _ _).mpr
      exact firstAligned.resolve_left fun firstHorizontal =>
        firstVerticalTag
          ((retainedCarrierNode_isHorizontal_iff
            graph firstEndpoints.1 firstAligned).mpr
              firstHorizontal)
    have secondHorizontal :
        (secondLink.first.supportingSegment graph).IsHorizontal := by
      exact
        (GridSegment.isHorizontal_translate _ _).mpr
          ((retainedCarrierNode_isHorizontal_iff
            graph secondEndpoints.1 secondAligned).mp
              secondHorizontalTag)
    rw [supportEqual] at firstVertical
    exact firstVertical.2 secondHorizontal.1

/-- Every genuine crossing of neighboring source occurrences is explicitly
present in the retained 5×5 crossing orbit. -/
theorem orientedCrossingHalo_subset_retainedCrossings
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    orientedCrossingHalo graph ⊆ retainedCrossings graph := by
  intro record recordMem
  have sound := orientedCrossingHalo_sound graph recordMem
  have pointBounds :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal sound.1 sound.2.2.1
        sound.2.2.2.2.2.2.2.1
  exact
    mem_retainedCrossings_of_periodNormalize_mem_of_shift_mem
      graph record
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal recordMem)
      (crossingPeriodShift_mem_retentionShifts
        graph record pointBounds)

end PeriodicOrthocrossing
end LeanTrominoes
