/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedTranslatedCarrierGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCarrierSeparation

/-!
# Separation of translated parallel retained carriers

The finite retained carrier list selects one owner per periodic orbit.
Planarity, however, compares every translate of that owner against every
other selected component.  This file extends the source-corridor argument to
such arbitrary translates.  No membership of the translated link in the
finite retention window is needed.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 2000000

/-- A translated horizontal selected link is rectangle-separated from a
selected horizontal link whenever their source intervals have disjoint open
interiors. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_support_disjoint
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
    (firstHorizontal : firstLink.first.isHorizontal = true)
    (secondHorizontal : secondLink.first.isHorizontal = true)
    (shift : Cell)
    (disjoint :
      ¬GridSegment.OpenIntervalsOverlap
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.1
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).finish.1
        (secondLink.first.supportingSegment graph).start.1
        (secondLink.first.supportingSegment graph).finish.1) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstBounds :=
    retainedDrawingCompleteCarrierLink_periodTranslate_horizontal_support_bounded
      wellFormed degree isLocal firstMem firstHorizontal shift
  have secondBounds :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal secondMem secondHorizontal
  simp only [planarMacroScale] at firstBounds secondBounds
  unfold GridSegment.OpenIntervalsOverlap at disjoint
  have separated :
      max
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).start.1
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).finish.1 ≤
          min (secondLink.first.supportingSegment graph).start.1
            (secondLink.first.supportingSegment graph).finish.1 ∨
        max (secondLink.first.supportingSegment graph).start.1
            (secondLink.first.supportingSegment graph).finish.1 ≤
          min
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).start.1
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).finish.1 := by
    omega
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second] at firstBounds separated
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.isHorizontal_periodTranslate,
    firstHorizontal, secondHorizontal, if_true]
  rcases separated with firstBefore | secondBefore
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

/-- A translated vertical selected link is rectangle-separated from a
selected vertical link whenever their source intervals have disjoint open
interiors. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_support_disjoint
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
    (firstVertical : ¬firstLink.first.isHorizontal = true)
    (secondVertical : ¬secondLink.first.isHorizontal = true)
    (shift : Cell)
    (disjoint :
      ¬GridSegment.OpenIntervalsOverlap
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.2
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).finish.2
        (secondLink.first.supportingSegment graph).start.2
        (secondLink.first.supportingSegment graph).finish.2) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstBounds :=
    retainedDrawingCompleteCarrierLink_periodTranslate_vertical_support_bounded
      wellFormed degree isLocal firstMem firstVertical shift
  have secondBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal secondMem secondVertical
  simp only [planarMacroScale] at firstBounds secondBounds
  unfold GridSegment.OpenIntervalsOverlap at disjoint
  have separated :
      max
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).start.2
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).finish.2 ≤
          min (secondLink.first.supportingSegment graph).start.2
            (secondLink.first.supportingSegment graph).finish.2 ∨
        max (secondLink.first.supportingSegment graph).start.2
            (secondLink.first.supportingSegment graph).finish.2 ≤
          min
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).start.2
            ((carrierLinkPeriodTranslate graph firstLink shift).first
              |>.supportingSegment graph).finish.2 := by
    omega
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second] at firstBounds separated
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.isHorizontal_periodTranslate,
    firstVertical, secondVertical, Bool.false_eq_true, if_false]
  rcases separated with firstBefore | secondBefore
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Translated horizontal selected links on different source rows have
strictly separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_normal_ne
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
    (firstHorizontal : firstLink.first.isHorizontal = true)
    (secondHorizontal : secondLink.first.isHorizontal = true)
    (shift : Cell)
    (normalDifferent :
      ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.2 ≠
        (secondLink.first.supportingSegment graph).start.2) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    retainedCarrierNode_periodTranslate_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1 shift
  have secondNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  simp only [carrierLinkPeriodTranslate_first] at normalDifferent
  simp only [CarrierNode.isHorizontal_periodTranslate,
    firstHorizontal, if_true] at firstNormal
  rw [if_pos secondHorizontal] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.isHorizontal_periodTranslate,
    firstHorizontal, secondHorizontal, if_true]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Translated vertical selected links on different source columns have
strictly separated physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_normal_ne
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
    (firstVertical : ¬firstLink.first.isHorizontal = true)
    (secondVertical : ¬secondLink.first.isHorizontal = true)
    (shift : Cell)
    (normalDifferent :
      ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.1 ≠
        (secondLink.first.supportingSegment graph).start.1) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
  have firstNormal :=
    retainedCarrierNode_periodTranslate_position_normalCoordinate
      wellFormed degree isLocal firstEndpoints.1 shift
  have secondNormal :=
    retainedCarrierNode_position_normalCoordinate
      wellFormed degree isLocal secondEndpoints.1
  simp only [carrierLinkPeriodTranslate_first] at normalDifferent
  simp only [CarrierNode.isHorizontal_periodTranslate,
    firstVertical, Bool.false_eq_true, if_false] at firstNormal
  rw [if_neg secondVertical] at secondNormal
  simp only [planarMacroScale] at firstNormal secondNormal
  unfold drawingCompleteCarrierLinkRectangleLower
    drawingCompleteCarrierLinkRectangleUpper
    ClosedGridRectanglesSeparated
  simp only [carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.isHorizontal_periodTranslate,
    firstVertical, secondVertical, Bool.false_eq_true, if_false]
  rcases lt_or_gt_of_ne normalDifferent with lower | higher
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

/-- A translated horizontal selected link and a selected horizontal link
with different physical occurrence keys have separated rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_key_ne
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
    (firstHorizontal : firstLink.first.isHorizontal = true)
    (secondHorizontal : secondLink.first.isHorizontal = true)
    (shift : Cell)
    (keyDifferent :
      (carrierLinkPeriodTranslate graph firstLink shift).first.carrierKey ≠
        secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases normalDifferent :
      ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.2 ≠
        (secondLink.first.supportingSegment graph).start.2
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_normal_ne
        wellFormed degree isLocal firstMem secondMem
        firstHorizontal secondHorizontal shift normalDifferent
  · have endpointsFirst :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
    have endpointsSecond :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
    have firstAligned :
        firstLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        firstLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
    have secondAligned :
        secondLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        secondLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
    have firstStoredHorizontal :
        firstLink.first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpointsFirst.1 firstAligned).mp firstHorizontal
    have secondStoredHorizontal :
        secondLink.first.indexed.segment.IsHorizontal :=
      (retainedCarrierNode_isHorizontal_iff
        graph endpointsSecond.1 secondAligned).mp secondHorizontal
    have firstSupportHorizontal :
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).IsHorizontal := by
      unfold CarrierNode.supportingSegment
      exact
        (GridSegment.isHorizontal_translate _ _).mpr
          (by simpa using firstStoredHorizontal)
    have secondSupportHorizontal :
        (secondLink.first.supportingSegment graph).IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr
        secondStoredHorizontal
    have occurrenceDifferent :
        PeriodicGridDrawing.SegmentOccurrenceKey
            (carrierLinkPeriodTranslate graph firstLink shift).first.indexed
            (carrierLinkPeriodTranslate graph firstLink shift).first.translate ≠
          PeriodicGridDrawing.SegmentOccurrenceKey
            secondLink.first.indexed secondLink.first.translate := by
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using
        keyDifferent
    have noContinuousMeet :=
      drawing_horizontalContinuousInteriors_disjoint
        wellFormed degree isLocal
        (retainedCarrierNode_periodTranslate_indexed_mem
          graph endpointsFirst.1 shift)
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
        firstSupportHorizontal secondSupportHorizontal
        occurrenceDifferent
    have axialDisjoint :
        ¬GridSegment.OpenIntervalsOverlap
          ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.supportingSegment graph).start.1
          ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.supportingSegment graph).finish.1
          (secondLink.first.supportingSegment graph).start.1
          (secondLink.first.supportingSegment graph).finish.1 := by
      intro overlap
      apply noContinuousMeet
      exact Or.inl
        ⟨firstSupportHorizontal, secondSupportHorizontal,
          not_ne_iff.mp normalDifferent, overlap⟩
    exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_support_disjoint
        wellFormed degree isLocal firstMem secondMem
        firstHorizontal secondHorizontal shift axialDisjoint

/-- A translated vertical selected link and a selected vertical link with
different physical occurrence keys have separated rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_key_ne
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
    (firstVertical : ¬firstLink.first.isHorizontal = true)
    (secondVertical : ¬secondLink.first.isHorizontal = true)
    (shift : Cell)
    (keyDifferent :
      (carrierLinkPeriodTranslate graph firstLink shift).first.carrierKey ≠
        secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases normalDifferent :
      ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).start.1 ≠
        (secondLink.first.supportingSegment graph).start.1
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_normal_ne
        wellFormed degree isLocal firstMem secondMem
        firstVertical secondVertical shift normalDifferent
  · have endpointsFirst :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph firstMem
    have endpointsSecond :=
      retainedDrawingCompleteCarrierLink_endpoints_mem graph secondMem
    have firstAligned :
        firstLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        firstLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsFirst.1)
    have secondAligned :
        secondLink.first.indexed.segment.IsAxisAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        secondLink.first.indexed
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
    have firstNotHorizontal :
        ¬firstLink.first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact firstVertical
        ((retainedCarrierNode_isHorizontal_iff
          graph endpointsFirst.1 firstAligned).mpr horizontal)
    have secondNotHorizontal :
        ¬secondLink.first.indexed.segment.IsHorizontal := by
      intro horizontal
      exact secondVertical
        ((retainedCarrierNode_isHorizontal_iff
          graph endpointsSecond.1 secondAligned).mpr horizontal)
    have firstStoredVertical :
        firstLink.first.indexed.segment.IsVertical :=
      firstAligned.resolve_left firstNotHorizontal
    have secondStoredVertical :
        secondLink.first.indexed.segment.IsVertical :=
      secondAligned.resolve_left secondNotHorizontal
    have firstSupportVertical :
        ((carrierLinkPeriodTranslate graph firstLink shift).first
          |>.supportingSegment graph).IsVertical := by
      unfold CarrierNode.supportingSegment
      exact
        (GridSegment.isVertical_translate _ _).mpr
          (by simpa using firstStoredVertical)
    have secondSupportVertical :
        (secondLink.first.supportingSegment graph).IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr
        secondStoredVertical
    have occurrenceDifferent :
        PeriodicGridDrawing.SegmentOccurrenceKey
            (carrierLinkPeriodTranslate graph firstLink shift).first.indexed
            (carrierLinkPeriodTranslate graph firstLink shift).first.translate ≠
          PeriodicGridDrawing.SegmentOccurrenceKey
            secondLink.first.indexed secondLink.first.translate := by
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using
        keyDifferent
    have noContinuousMeet :=
      drawing_verticalContinuousInteriors_disjoint
        wellFormed degree isLocal
        (retainedCarrierNode_periodTranslate_indexed_mem
          graph endpointsFirst.1 shift)
        (retainedCarrierNode_indexed_mem graph endpointsSecond.1)
        firstSupportVertical secondSupportVertical
        occurrenceDifferent
    have axialDisjoint :
        ¬GridSegment.OpenIntervalsOverlap
          ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.supportingSegment graph).start.2
          ((carrierLinkPeriodTranslate graph firstLink shift).first
            |>.supportingSegment graph).finish.2
          (secondLink.first.supportingSegment graph).start.2
          (secondLink.first.supportingSegment graph).finish.2 := by
      intro overlap
      apply noContinuousMeet
      exact Or.inr
        (Or.inl
          ⟨firstSupportVertical, secondSupportVertical,
            not_ne_iff.mp normalDifferent, overlap⟩)
    exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_support_disjoint
        wellFormed degree isLocal firstMem secondMem
        firstVertical secondVertical shift axialDisjoint

/-- Different-key translated selected links on a common axis have separated
physical rectangles. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_parallel_key_ne
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
    (shift : Cell)
    (notPerpendicular :
      ¬CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate graph firstLink shift) secondLink)
    (keyDifferent :
      (carrierLinkPeriodTranslate graph firstLink shift).first.carrierKey ≠
        secondLink.first.carrierKey) :
    ClosedGridRectanglesSeparated
      (drawingCompleteCarrierLinkRectangleLower graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleUpper graph
        (carrierLinkPeriodTranslate graph firstLink shift))
      (drawingCompleteCarrierLinkRectangleLower graph secondLink)
      (drawingCompleteCarrierLinkRectangleUpper graph secondLink) := by
  by_cases firstHorizontal :
      firstLink.first.isHorizontal = true
  · by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · exact
        retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_horizontal_key_ne
          wellFormed degree isLocal firstMem secondMem
          firstHorizontal secondHorizontal shift keyDifferent
    · exact False.elim
        (notPerpendicular
          (Or.inl
            ⟨by simpa using firstHorizontal, secondHorizontal⟩))
  · by_cases secondHorizontal :
        secondLink.first.isHorizontal = true
    · exact False.elim
        (notPerpendicular
          (Or.inr
            ⟨by simpa using firstHorizontal, secondHorizontal⟩))
    · exact
        retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_vertical_key_ne
          wellFormed degree isLocal firstMem secondMem
          firstHorizontal secondHorizontal shift keyDifferent

/-- Rectangle separation gives route separation when the first selected
carrier lens is viewed in an arbitrary period translate. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_rectanglesSeparated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (shift : Cell)
    (rectanglesSeparated :
      ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower formula.incidenceGraph
          (carrierLinkPeriodTranslate formula.incidenceGraph
            firstLink shift))
        (drawingCompleteCarrierLinkRectangleUpper formula.incidenceGraph
          (carrierLinkPeriodTranslate formula.incidenceGraph
            firstLink shift))
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph secondLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph secondLink))
    {firstClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    {firstLiteral : PlanarSATVariable Variable × Bool}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    {secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    {secondLiteral : PlanarSATVariable Variable × Bool}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing formula
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)).routes firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  have firstDrawingBounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
      wellFormed degree isLocal firstMem
  have secondDrawingBounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded
      wellFormed degree isLocal secondMem
  apply
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro translatedPoint translatedPointMember
    rw [
      drawingPlanarSATCarrierLensIncidenceDrawing_routes_periodTranslate]
      at translatedPointMember
    unfold translatePolyline at translatedPointMember
    rcases List.mem_map.mp translatedPointMember with
      ⟨point, pointMember, pointEq⟩
    subst translatedPoint
    have pointBounded :
        InClosedGridRectangle
          (drawingCompleteCarrierLinkRectangleLower
            formula.incidenceGraph firstLink)
          (drawingCompleteCarrierLinkRectangleUpper
            formula.incidenceGraph firstLink)
          point :=
      firstDrawingBounded.of_members
        firstClauseMember firstLiteralMember pointMember
    show
      InClosedGridRectangle
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph
          (carrierLinkPeriodTranslate formula.incidenceGraph
            firstLink shift))
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph
          (carrierLinkPeriodTranslate formula.incidenceGraph
            firstLink shift))
        (Cell.add
          (carrierMacroPeriodTranslation
            formula.incidenceGraph shift)
          point)
    rw [
      drawingCompleteCarrierLinkRectangleLower_periodTranslate,
      drawingCompleteCarrierLinkRectangleUpper_periodTranslate]
    rcases lowerEq :
        drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph firstLink with ⟨lowerX, lowerY⟩
    rcases upperEq :
        drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph firstLink with ⟨upperX, upperY⟩
    rcases offsetEq :
        carrierMacroPeriodTranslation
          formula.incidenceGraph shift with ⟨offsetX, offsetY⟩
    rcases point with ⟨pointX, pointY⟩
    simp only [lowerEq, upperEq,
      InClosedGridRectangle, Cell.add] at pointBounded ⊢
    omega
  · intro point pointMember
    exact
      secondDrawingBounded.of_members
        secondClauseMember secondLiteralMember pointMember
  · exact rectanglesSeparated

/-- Every genuine route pair from a translated selected carrier and a
different-key parallel selected carrier avoids one another. -/
theorem
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_parallel_key_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (secondMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        formula.incidenceGraph)
    (shift : Cell)
    (notPerpendicular :
      ¬CarrierLinksPerpendicular
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)
        secondLink)
    (keyDifferent :
      (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift).first.carrierKey ≠
        secondLink.first.carrierKey)
    {firstClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula firstLink).formula.zipIdx)
    {firstLiteral : PlanarSATVariable Variable × Bool}
    {firstLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    {secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {secondClauseIndex : Nat}
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula secondLink).formula.zipIdx)
    {secondLiteral : PlanarSATVariable Variable × Bool}
    {secondLiteralIndex : Nat}
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing formula
        (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift)).routes firstClauseIndex firstLiteralIndex)
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).routes
          secondClauseIndex secondLiteralIndex) := by
  apply
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_periodTranslate_of_rectanglesSeparated
      wellFormed degree isLocal firstMem secondMem shift
  · exact
      retainedDrawingCompleteCarrierLink_periodTranslate_rectanglesSeparated_of_parallel_key_ne
        wellFormed degree isLocal firstMem secondMem shift
        notPerpendicular keyDifferent
  · exact firstClauseMember
  · exact firstLiteralMember
  · exact secondClauseMember
  · exact secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
