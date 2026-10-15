/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryMatching

/-! # A simple, pairwise disjoint orthogonal router for boundary matchings -/
namespace LeanTrominoes.OrthogonalBoundaryRouting
open PeriodicOrthocrossing

theorem matchingRoute_orthogonal {chords : Finset Chord} {width height : Int} {chord : Chord}
    (member : chord ∈ chords) (room : 2*(chords.card : Int) < width ∧ 2*(chords.card : Int) < height)
    (firstInside : chord.1.Inside width height chords.card) (lastInside : chord.2.Inside width height chords.card)
    (ordered : chord.1.Before chord.2) : OrthogonalPolyline (matchingRoute chords width height chord) :=
  route_orthogonal (by exact_mod_cast matchingDepth_positive chords chord)
    (by exact_mod_cast matchingDepth_le_card member) room firstInside lastInside ordered

theorem matchingRoute_isRealOpenSimple {chords : Finset Chord} {width height : Int} {chord : Chord}
    (member : chord ∈ chords) (room : 2*(chords.card : Int) < width ∧ 2*(chords.card : Int) < height)
    (firstInside : chord.1.Inside width height chords.card) (lastInside : chord.2.Inside width height chords.card)
    (ordered : chord.1.Before chord.2) : GridPolyline.IsRealOpenSimple (matchingRoute chords width height chord) :=
  route_isRealOpenSimple (by exact_mod_cast matchingDepth_positive chords chord)
    (by exact_mod_cast matchingDepth_le_card member) room firstInside lastInside ordered

theorem matchingRoutes_disjoint {chords : Finset Chord} {width height : Int} {first second : Chord}
    (firstMember : first ∈ chords) (secondMember : second ∈ chords) (different : first ≠ second)
    (room : 2*(chords.card : Int) < width ∧ 2*(chords.card : Int) < height)
    (firstInside : first.1.Inside width height chords.card) (lastInside : first.2.Inside width height chords.card)
    (secondFirstInside : second.1.Inside width height chords.card) (secondLastInside : second.2.Inside width height chords.card)
    (firstOrder : first.1.Before first.2) (secondOrder : second.1.Before second.2)
    (noninterlacing : Noninterlacing first second) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (matchingRoute chords width height first) point)
    (secondContains : GridPolyline.RealContains (matchingRoute chords width height second) point) : False := by
  have firstPositive : (0 : Int) < matchingDepth chords first := by exact_mod_cast matchingDepth_positive chords first
  have secondPositive : (0 : Int) < matchingDepth chords second := by exact_mod_cast matchingDepth_positive chords second
  have firstBound : (matchingDepth chords first : Int) ≤ chords.card := by exact_mod_cast matchingDepth_le_card firstMember
  have secondBound : (matchingDepth chords second : Int) ≤ chords.card := by exact_mod_cast matchingDepth_le_card secondMember
  have depthsDifferent : matchingDepth chords first ≠ matchingDepth chords second :=
    fun equal => different (matchingDepth_injective chords firstMember secondMember equal)
  rcases lt_or_gt_of_ne depthsDifferent with order | order
  · have outside := deeper_endpoints_outside firstMember secondMember firstOrder secondOrder noninterlacing order
    exact shallow_route_disjoint firstPositive secondPositive firstBound secondBound (by exact_mod_cast order)
      room firstInside lastInside secondFirstInside secondLastInside firstOrder secondOrder
      (noninterlacing_endpoints_ne firstOrder secondOrder noninterlacing) outside.1 outside.2 firstContains secondContains
  · have outside := deeper_endpoints_outside secondMember firstMember secondOrder firstOrder noninterlacing.symm order
    exact shallow_route_disjoint secondPositive firstPositive secondBound firstBound (by exact_mod_cast order)
      room secondFirstInside secondLastInside firstInside lastInside secondOrder firstOrder
      (noninterlacing_endpoints_ne secondOrder firstOrder noninterlacing.symm) outside.1 outside.2 secondContains firstContains

end LeanTrominoes.OrthogonalBoundaryRouting
