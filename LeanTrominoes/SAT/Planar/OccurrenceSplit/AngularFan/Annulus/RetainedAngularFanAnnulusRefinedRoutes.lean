/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Annulus.RetainedAngularFanAnnulusRoutes
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineStrictSeparationCheck
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineSegmentBoxCheck
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Annulus.RetainedAngularFanAnnulusRouteTable

/-!
# Coordinated refined routes across the retained fan annulus

The base annulus is uniformly refined by eight.  At each successive square
radius, a route linearly interpolates its normalized clockwise coordinate
between the direction-and-slot outer port and the fixed compass anchor.
Successive samples are joined by a side-following orthogonal elbow.

The factor-eight spacing is large enough that every two order-compatible
routes are strictly separated.  This is checked over the finite set of
eleven retained directions and eight slots, rather than over the much larger
raw terminal-shape type.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Uniform local refinement used by the coordinated annular router. -/
def retainedTerminalFanRoutingRefinement : Nat := 8

/-- Number of unit radial layers between the refined radius-33 and radius-22
frames. -/
def retainedTerminalFanRoutingDepth : Nat :=
  11 * retainedTerminalFanRoutingRefinement

/-- Clockwise point at a unit boundary index on a square of the given
coordinate radius. -/
def retainedTerminalSquareBoundaryPoint
    (radius index : Nat) : Cell :=
  let r : Int := radius
  let q : Int := index
  if index ≤ radius then
    (r, q)
  else if index ≤ 3 * radius then
    (2 * r - q, r)
  else if index ≤ 5 * radius then
    (-r, 4 * r - q)
  else if index ≤ 7 * radius then
    (q - 6 * r, -r)
  else
    (r, q - 8 * r)

/-- Rounded clockwise boundary index of one route at a radial depth. -/
def retainedTerminalFanRoutingBoundaryIndex
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Nat :=
  let totalDepth := retainedTerminalFanRoutingDepth
  let radius :=
    33 * retainedTerminalFanRoutingRefinement - depth
  let outerIndex :=
    8 * direction.angularRank + slot.val
  let angularNumerator :=
    (totalDepth - depth) * outerIndex +
      11 * depth * slot.val
  let denominator := 88 * totalDepth
  (8 * radius * angularNumerator + denominator / 2) /
    denominator

/-- Refined square-boundary sample of one interpolated annular route. -/
def retainedTerminalFanRoutingSample
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot)
    (depth : Nat) : Cell :=
  retainedTerminalSquareBoundaryPoint
    (33 * retainedTerminalFanRoutingRefinement - depth)
    (retainedTerminalFanRoutingBoundaryIndex
      direction slot depth)

/-- Orthogonal elbow between consecutive interpolated samples.  On a
vertical square side it moves vertically first; on a horizontal side it
moves horizontally first. -/
def retainedTerminalFanRoutingStep
    (first second : Cell) : List Cell :=
  let radius := max first.1.natAbs first.2.natAbs
  (if first.1.natAbs = radius then
      [first, (first.1, second.2), second]
    else
      [first, (second.1, first.2), second]).dedup

/-- Join the elbows between every consecutive pair of samples. -/
def retainedTerminalFanConnectSamples : List Cell → List Cell
  | [] => []
  | first :: rest =>
      match rest with
      | [] => [first]
      | second :: _ =>
          joinAtEndpoint
            (retainedTerminalFanRoutingStep first second)
            (retainedTerminalFanConnectSamples rest)

/-- The refined sample list from the outer frame through the inner frame. -/
def retainedTerminalFanRoutingSamples
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  (List.range (retainedTerminalFanRoutingDepth + 1)).map
    (retainedTerminalFanRoutingSample direction slot)

/-- Coordinated finite annular route selected by a direction and occurrence
slot. -/
def retainedTerminalFanComputedAnnulusRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  retainedTerminalFanConnectSamples
    (retainedTerminalFanRoutingSamples direction slot)

/-- Coordinated routes with their verified interpolation already evaluated. -/
def retainedTerminalFanRefinedAnnulusRoute
    (direction : RetainedTerminalDirection) (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanCachedAnnulusRoutes direction).getD slot.val []

private theorem retainedTerminalFanCachedAnnulusRoute_case0 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case1 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case2 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case3 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case4 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case5 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case6 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case7 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.east)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case8 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case9 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case10 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case11 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case12 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case13 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case14 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case15 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.left)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case16 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case17 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case18 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case19 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case20 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case21 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case22 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case23 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southeast)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case24 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case25 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case26 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case27 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case28 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case29 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case30 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case31 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.south)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case32 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case33 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case34 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case35 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case36 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case37 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case38 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case39 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.right)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case40 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case41 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case42 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case43 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case44 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case45 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case46 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case47 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.southwest)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case48 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case49 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case50 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case51 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case52 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case53 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case54 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case55 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.west)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case56 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case57 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case58 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case59 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case60 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case61 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case62 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case63 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northwest)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case64 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case65 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case66 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case67 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case68 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case69 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case70 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case71 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.north)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case72 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case73 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case74 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case75 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case76 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case77 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case78 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case79 :
    retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.compass (.northeast)) 7 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case80 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 0 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 0 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case81 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 1 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 1 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case82 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 2 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 2 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case83 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 3 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 3 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case84 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 4 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 4 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case85 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 5 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 5 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case86 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 6 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 6 := by
  decide +kernel

private theorem retainedTerminalFanCachedAnnulusRoute_case87 :
    retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) 7 =
      retainedTerminalFanComputedAnnulusRoute (.routedClause (.middle)) 7 := by
  decide +kernel

/-- Every stored route is exactly the original interpolated orthogonal route. -/
theorem retainedTerminalFanRefinedAnnulusRoute_eq_computed
    (direction : RetainedTerminalDirection) (slot : RetainedTerminalSlot) :
    retainedTerminalFanRefinedAnnulusRoute direction slot =
      retainedTerminalFanComputedAnnulusRoute direction slot := by
  have cases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 ∨
      slot.val = 4 ∨ slot.val = 5 ∨ slot.val = 6 ∨ slot.val = 7 := by
    have bound := slot.is_lt
    omega
  rcases cases with h | h | h | h | h | h | h | h
  · have slotEq : slot = 0 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case0
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case16
        | south => exact retainedTerminalFanCachedAnnulusRoute_case24
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case40
        | west => exact retainedTerminalFanCachedAnnulusRoute_case48
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case56
        | north => exact retainedTerminalFanCachedAnnulusRoute_case64
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case72
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case8
        | right => exact retainedTerminalFanCachedAnnulusRoute_case32
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case80
  · have slotEq : slot = 1 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case1
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case17
        | south => exact retainedTerminalFanCachedAnnulusRoute_case25
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case41
        | west => exact retainedTerminalFanCachedAnnulusRoute_case49
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case57
        | north => exact retainedTerminalFanCachedAnnulusRoute_case65
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case73
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case9
        | right => exact retainedTerminalFanCachedAnnulusRoute_case33
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case81
  · have slotEq : slot = 2 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case2
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case18
        | south => exact retainedTerminalFanCachedAnnulusRoute_case26
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case42
        | west => exact retainedTerminalFanCachedAnnulusRoute_case50
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case58
        | north => exact retainedTerminalFanCachedAnnulusRoute_case66
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case74
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case10
        | right => exact retainedTerminalFanCachedAnnulusRoute_case34
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case82
  · have slotEq : slot = 3 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case3
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case19
        | south => exact retainedTerminalFanCachedAnnulusRoute_case27
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case43
        | west => exact retainedTerminalFanCachedAnnulusRoute_case51
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case59
        | north => exact retainedTerminalFanCachedAnnulusRoute_case67
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case75
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case11
        | right => exact retainedTerminalFanCachedAnnulusRoute_case35
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case83
  · have slotEq : slot = 4 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case4
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case20
        | south => exact retainedTerminalFanCachedAnnulusRoute_case28
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case44
        | west => exact retainedTerminalFanCachedAnnulusRoute_case52
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case60
        | north => exact retainedTerminalFanCachedAnnulusRoute_case68
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case76
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case12
        | right => exact retainedTerminalFanCachedAnnulusRoute_case36
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case84
  · have slotEq : slot = 5 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case5
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case21
        | south => exact retainedTerminalFanCachedAnnulusRoute_case29
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case45
        | west => exact retainedTerminalFanCachedAnnulusRoute_case53
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case61
        | north => exact retainedTerminalFanCachedAnnulusRoute_case69
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case77
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case13
        | right => exact retainedTerminalFanCachedAnnulusRoute_case37
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case85
  · have slotEq : slot = 6 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case6
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case22
        | south => exact retainedTerminalFanCachedAnnulusRoute_case30
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case46
        | west => exact retainedTerminalFanCachedAnnulusRoute_case54
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case62
        | north => exact retainedTerminalFanCachedAnnulusRoute_case70
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case78
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case14
        | right => exact retainedTerminalFanCachedAnnulusRoute_case38
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case86
  · have slotEq : slot = 7 := Fin.ext h
    subst slot
    cases direction with
    | compass port =>
        cases port with
        | east => exact retainedTerminalFanCachedAnnulusRoute_case7
        | southeast => exact retainedTerminalFanCachedAnnulusRoute_case23
        | south => exact retainedTerminalFanCachedAnnulusRoute_case31
        | southwest => exact retainedTerminalFanCachedAnnulusRoute_case47
        | west => exact retainedTerminalFanCachedAnnulusRoute_case55
        | northwest => exact retainedTerminalFanCachedAnnulusRoute_case63
        | north => exact retainedTerminalFanCachedAnnulusRoute_case71
        | northeast => exact retainedTerminalFanCachedAnnulusRoute_case79
    | routedClause arm =>
        cases arm with
        | left => exact retainedTerminalFanCachedAnnulusRoute_case15
        | right => exact retainedTerminalFanCachedAnnulusRoute_case39
        | middle => exact retainedTerminalFanCachedAnnulusRoute_case87

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- The first interpolated sample is the factor-eight refinement of the
exact radius-33 fan port. -/
theorem retainedTerminalFanRoutingSample_zero :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanRoutingSample direction slot 0 =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset
            (retainedTerminalFanPort direction slot)) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide (retainedTerminalFanRoutingSample direction slot 0 =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset (retainedTerminalFanPort direction slot)))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- The last interpolated sample is the factor-eight refinement of the exact
radius-22 compass anchor. -/
theorem retainedTerminalFanRoutingSample_last :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      retainedTerminalFanRoutingSample direction slot
          retainedTerminalFanRoutingDepth =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalAdapterPortOffset
            (retainedTerminalFanAnchorPort slot)) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide (retainedTerminalFanRoutingSample direction slot retainedTerminalFanRoutingDepth =
        Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalAdapterPortOffset (retainedTerminalFanAnchorPort slot)))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every coordinated route starts at its exact refined fan-facing port. -/
@[simp]
theorem retainedTerminalFanRefinedAnnulusRoute_head? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanRefinedAnnulusRoute
        direction slot).head? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalFanPortOffset
                (retainedTerminalFanPort direction slot))) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanRefinedAnnulusRoute direction slot).head? =
        some (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset (retainedTerminalFanPort direction slot))))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every coordinated route ends at its exact refined compass anchor. -/
@[simp]
theorem retainedTerminalFanRefinedAnnulusRoute_getLast? :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      (retainedTerminalFanRefinedAnnulusRoute
        direction slot).getLast? =
          some
            (Cell.scale retainedTerminalFanRoutingRefinement
              (retainedTerminalAdapterPortOffset
                (retainedTerminalFanAnchorPort slot))) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanRefinedAnnulusRoute direction slot).getLast? =
        some (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalAdapterPortOffset (retainedTerminalFanAnchorPort slot))))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every coordinated route is an orthogonal polyline. -/
theorem retainedTerminalFanRefinedAnnulusRoute_orthogonal :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot),
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanRefinedAnnulusRoute direction slot) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (gridPolylineSegments (retainedTerminalFanRefinedAnnulusRoute direction slot)).all fun segment =>
        decide segment.IsAxisAligned) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq,
    ← PeriodicOrthocrossing.orthogonalPolyline_iff_segments] using checked

/-- Every listed route point stays inside the refined radius-33 frame and
outside the refined radius-22 fan-anchor frame, except for its inner endpoint
on that frame. -/
theorem retainedTerminalFanRefinedAnnulusRoute_points_in_shell :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedAnnulusRoute direction slot →
        WithinCoordinateRadius
            (33 * retainedTerminalFanRoutingRefinement)
            (0, 0) point ∧
          ¬ WithinCoordinateRadius
            (22 * retainedTerminalFanRoutingRefinement - 1)
            (0, 0) point := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (retainedTerminalFanRefinedAnnulusRoute direction slot).all fun point =>
        decide (WithinCoordinateRadius (33 * retainedTerminalFanRoutingRefinement) (0, 0) point ∧
          ¬ WithinCoordinateRadius (22 * retainedTerminalFanRoutingRefinement - 1) (0, 0) point)) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

private theorem annulusSegmentBoxes_case0 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.east) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.east)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case1 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.left) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.routedClause (.left)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case2 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.southeast)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case3 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.south) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.south)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case4 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.right) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.routedClause (.right)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case5 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.southwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.southwest)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case6 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.west) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.west)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case7 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northwest) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.northwest)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case8 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.north) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.north)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case9 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.compass (.northeast) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.compass (.northeast)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

private theorem annulusSegmentBoxes_case10 :
    (finiteAll fun secondDirection : RetainedTerminalDirection =>
      finiteAll fun firstSlot : RetainedTerminalSlot =>
      finiteAll fun secondSlot : RetainedTerminalSlot =>
        guardedCheck ((.routedClause (.middle) : RetainedTerminalDirection).angularRank ≤ secondDirection.angularRank ∧ firstSlot.val < secondSlot.val)
          (segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute (.routedClause (.middle)) firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot))) = true := by
  decide +kernel

/-- Two routes whose outer directions and inner slots occur in the same
strict clockwise order have complete continuous separation. -/
theorem retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther :
    ∀ (firstDirection secondDirection :
        RetainedTerminalDirection)
      (firstSlot secondSlot : RetainedTerminalSlot),
      firstDirection.angularRank ≤ secondDirection.angularRank →
      firstSlot.val < secondSlot.val →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnnulusRoute
            firstDirection firstSlot)
          (retainedTerminalFanRefinedAnnulusRoute
            secondDirection secondSlot) := by
  intro firstDirection secondDirection firstSlot secondSlot directionsLe slotsLt
  have checked :
      ∀ secondDirection firstSlot secondSlot,
        firstDirection.angularRank ≤ secondDirection.angularRank →
        firstSlot.val < secondSlot.val →
          segmentBoxesSeparateCheck
            (retainedTerminalFanRefinedAnnulusRoute firstDirection firstSlot)
            (retainedTerminalFanRefinedAnnulusRoute secondDirection secondSlot) = true := by
    cases firstDirection with
    | compass port =>
      cases port with
      | east => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case0
      | southeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case2
      | south => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case3
      | southwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case5
      | west => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case6
      | northwest => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case7
      | north => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case8
      | northeast => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case9
    | routedClause arm =>
      cases arm with
      | left => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case1
      | right => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case4
      | middle => simpa only [finiteAll_eq_true, guardedCheck_eq_true, and_imp] using annulusSegmentBoxes_case10
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked secondDirection firstSlot secondSlot directionsLe slotsLt)

/-- Factor-eight refinement of the fixed inward compass-anchor route. -/
def retainedTerminalFanRefinedAnchorRoute
    (slot : RetainedTerminalSlot) : List Cell :=
  (retainedTerminalFanAnchorRoute slot).map
    (Cell.scale retainedTerminalFanRoutingRefinement)

/-- A refined anchor route starts at the refined radius-22 anchor. -/
@[simp]
theorem retainedTerminalFanRefinedAnchorRoute_head? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanRefinedAnchorRoute slot).head? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (retainedTerminalAdapterPortOffset
              (retainedTerminalFanAnchorPort slot))) := by
  have checked : (finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanRefinedAnchorRoute slot).head? =
        some (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalAdapterPortOffset (retainedTerminalFanAnchorPort slot))))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- A refined anchor route ends at the matching refined Figure 7 boundary
site. -/
@[simp]
theorem retainedTerminalFanRefinedAnchorRoute_getLast? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanRefinedAnchorRoute slot).getLast? =
        some
          (Cell.scale retainedTerminalFanRoutingRefinement
            (angularFanBoundaryOffset slot.val)) := by
  have checked : (finiteAll fun slot : RetainedTerminalSlot =>
      decide ((retainedTerminalFanRefinedAnchorRoute slot).getLast? =
        some (Cell.scale retainedTerminalFanRoutingRefinement (angularFanBoundaryOffset slot.val)))) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every refined inward anchor route is orthogonal. -/
theorem retainedTerminalFanRefinedAnchorRoute_orthogonal :
    ∀ slot : RetainedTerminalSlot,
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanRefinedAnchorRoute slot) := by
  have checked : (finiteAll fun slot : RetainedTerminalSlot =>
      (gridPolylineSegments (retainedTerminalFanRefinedAnchorRoute slot)).all fun segment =>
        decide segment.IsAxisAligned) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq,
    ← PeriodicOrthocrossing.orthogonalPolyline_iff_segments] using checked

/-- Different refined inward anchor routes are strictly separated. -/
theorem retainedTerminalFanRefinedAnchorRoutes_strictlyAvoidEachOther :
    ∀ first second : RetainedTerminalSlot,
      first ≠ second →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnchorRoute first)
          (retainedTerminalFanRefinedAnchorRoute second) := by
  have checked : (finiteAll fun first : RetainedTerminalSlot =>
      finiteAll fun second : RetainedTerminalSlot => guardedCheck (first ≠ second)
        (segmentBoxesSeparateCheck (retainedTerminalFanRefinedAnchorRoute first)
          (retainedTerminalFanRefinedAnchorRoute second))) = true := by
    decide +kernel
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  intro first second different
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _ (checked first second different)

/-- An annular route is strictly separated from every other slot's inward
anchor route. -/
theorem retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor :
    ∀ (direction : RetainedTerminalDirection)
      (annulusSlot anchorSlot : RetainedTerminalSlot),
      annulusSlot ≠ anchorSlot →
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanRefinedAnnulusRoute
            direction annulusSlot)
          (retainedTerminalFanRefinedAnchorRoute anchorSlot) := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection =>
      finiteAll fun annulusSlot : RetainedTerminalSlot =>
      finiteAll fun anchorSlot : RetainedTerminalSlot => guardedCheck (annulusSlot ≠ anchorSlot)
        (segmentBoxesSeparateCheck (retainedTerminalFanRefinedAnnulusRoute direction annulusSlot)
          (retainedTerminalFanRefinedAnchorRoute anchorSlot))) = true := by
    decide +kernel
  simp only [finiteAll_eq_true, guardedCheck_eq_true] at checked
  intro direction annulusSlot anchorSlot different
  exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _
    (checked direction annulusSlot anchorSlot different)

/-- Complete refined route from one occurrence-ordered fan port to the
matching refined Figure 7 boundary site. -/
def retainedTerminalFanRefinedRoute
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanRefinedAnnulusRoute direction slot)
    (retainedTerminalFanRefinedAnchorRoute slot)

/-- Every complete refined route starts at its refined fan-facing port. -/
@[simp]
theorem retainedTerminalFanRefinedRoute_head?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRoute direction slot).head? =
      some
        (Cell.scale retainedTerminalFanRoutingRefinement
          (retainedTerminalFanPortOffset
            (retainedTerminalFanPort direction slot))) := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanRefinedAnnulusRoute_head?
      direction slot)

/-- Every complete refined route ends at its matching refined Figure 7
boundary site. -/
@[simp]
theorem retainedTerminalFanRefinedRoute_getLast?
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanRefinedRoute direction slot).getLast? =
      some
        (Cell.scale retainedTerminalFanRoutingRefinement
          (angularFanBoundaryOffset slot.val)) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanRefinedAnnulusRoute_getLast?
      direction slot)
    (retainedTerminalFanRefinedAnchorRoute_head? slot)
    (retainedTerminalFanRefinedAnchorRoute_getLast? slot)

/-- Every complete refined fan route is orthogonal. -/
theorem retainedTerminalFanRefinedRoute_orthogonal
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanRefinedRoute direction slot) := by
  exact
    PeriodicOrthocrossing.OrthogonalPolyline.joinAtEndpoint
      (retainedTerminalFanRefinedAnnulusRoute_orthogonal
        direction slot)
      (retainedTerminalFanRefinedAnchorRoute_orthogonal slot)
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        direction slot)
      (retainedTerminalFanRefinedAnchorRoute_head? slot)

/-- Every listed point of a complete refined route remains outside the
interior of the refined radius-12 Figure 7 square. -/
theorem retainedTerminalFanRefinedRoute_points_outside_fan :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedRoute direction slot →
        ¬ WithinCoordinateRadius
          (12 * retainedTerminalFanRoutingRefinement - 1)
          (0, 0) point := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (retainedTerminalFanRefinedRoute direction slot).all fun point =>
        decide (¬ WithinCoordinateRadius (12 * retainedTerminalFanRoutingRefinement - 1) (0, 0) point)) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Every listed point of a complete refined route remains inside the
refined radius-33 outer frame. -/
theorem retainedTerminalFanRefinedRoute_points_within_outer_frame :
    ∀ (direction : RetainedTerminalDirection)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanRefinedRoute direction slot →
        WithinCoordinateRadius
          (33 * retainedTerminalFanRoutingRefinement)
          (0, 0) point := by
  have checked : (finiteAll fun direction : RetainedTerminalDirection => finiteAll fun slot : RetainedTerminalSlot =>
      (retainedTerminalFanRefinedRoute direction slot).all fun point =>
        decide (WithinCoordinateRadius (33 * retainedTerminalFanRoutingRefinement) (0, 0) point)) = true := by
    decide +kernel
  simpa only [finiteAll_eq_true, List.all_eq_true, decide_eq_true_eq] using checked

/-- Complete refined routes with order-compatible endpoints are strictly
separated. -/
theorem retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
    (firstDirection secondDirection : RetainedTerminalDirection)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (directionsLe :
      firstDirection.angularRank ≤ secondDirection.angularRank)
    (slotsLt : firstSlot.val < secondSlot.val) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedRoute
        firstDirection firstSlot)
      (retainedTerminalFanRefinedRoute
        secondDirection secondSlot) := by
  have slotsNe : firstSlot ≠ secondSlot := by
    intro slotsEq
    subst secondSlot
    exact Nat.lt_irrefl _ slotsLt
  have annulusAvoidAnnulus :=
    retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther
      firstDirection secondDirection firstSlot secondSlot
      directionsLe slotsLt
  have annulusAvoidSecondAnchor :=
    retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor
      firstDirection firstSlot secondSlot slotsNe
  have firstAnchorAvoidAnnulus :=
    (retainedTerminalFanRefinedAnnulusRoute_strictlyAvoid_anchor
      secondDirection secondSlot firstSlot slotsNe.symm).symm
  have anchorsAvoid :=
    retainedTerminalFanRefinedAnchorRoutes_strictlyAvoidEachOther
      firstSlot secondSlot slotsNe
  have completeFirstAvoidAnnulus :=
    annulusAvoidAnnulus.join_left firstAnchorAvoidAnnulus
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedAnchorRoute_head? firstSlot)
  have completeFirstAvoidAnchor :=
    annulusAvoidSecondAnchor.join_left anchorsAvoid
      (retainedTerminalFanRefinedAnnulusRoute_getLast?
        firstDirection firstSlot)
      (retainedTerminalFanRefinedAnchorRoute_head? firstSlot)
  exact completeFirstAvoidAnnulus.join_right
    completeFirstAvoidAnchor
    (retainedTerminalFanRefinedAnnulusRoute_getLast?
      secondDirection secondSlot)
    (retainedTerminalFanRefinedAnchorRoute_head? secondSlot)

/-- Optional coordinated annular route selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanRefinedAnnulusRoute
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Option (List Cell) :=
  (shape.direction slot).map fun direction =>
    retainedTerminalFanRefinedAnnulusRoute direction slot

/-- Active slots select their exact direction-and-slot route. -/
theorem RetainedAngularTerminalShape.fanRefinedAnnulusRoute_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq : shape.direction slot = some direction) :
    shape.fanRefinedAnnulusRoute slot =
      some
        (retainedTerminalFanRefinedAnnulusRoute
          direction slot) := by
  simp [fanRefinedAnnulusRoute, directionEq]

/-- Distinct active routes of a valid finite shape are strictly separated. -/
theorem RetainedAngularTerminalShape.fanRefinedAnnulusRoutes_strictlyAvoid
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedAnnulusRoute
        firstDirection first)
      (retainedTerminalFanRefinedAnnulusRoute
        secondDirection second) := by
  exact
    retainedTerminalFanRefinedAnnulusRoutes_strictlyAvoidEachOther
      firstDirection secondDirection first second
      (valid.2.1 first second firstDirection secondDirection
        slotsLt firstDirectionEq secondDirectionEq)
      slotsLt

/-- Optional complete refined fan route selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanRefinedRoute
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Option (List Cell) :=
  (shape.direction slot).map fun direction =>
    retainedTerminalFanRefinedRoute direction slot

/-- An active slot selects its complete exact direction-and-slot route. -/
theorem RetainedAngularTerminalShape.fanRefinedRoute_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq : shape.direction slot = some direction) :
    shape.fanRefinedRoute slot =
      some
        (retainedTerminalFanRefinedRoute direction slot) := by
  simp [fanRefinedRoute, directionEq]

/-- An inactive slot selects no complete refined route. -/
theorem RetainedAngularTerminalShape.fanRefinedRoute_eq_none
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (directionEq : shape.direction slot = none) :
    shape.fanRefinedRoute slot = none := by
  simp [fanRefinedRoute, directionEq]

/-- Complete routes of distinct active slots in a valid shape are strictly
separated. -/
theorem RetainedAngularTerminalShape.fanRefinedRoutes_strictlyAvoid
    (shape : RetainedAngularTerminalShape)
    (valid : shape.IsValid)
    (first second : RetainedTerminalSlot)
    (firstDirection secondDirection : RetainedTerminalDirection)
    (slotsLt : first.val < second.val)
    (firstDirectionEq :
      shape.direction first = some firstDirection)
    (secondDirectionEq :
      shape.direction second = some secondDirection) :
    RoutesStrictlyAvoidEachOther
      (retainedTerminalFanRefinedRoute
        firstDirection first)
      (retainedTerminalFanRefinedRoute
        secondDirection second) := by
  exact retainedTerminalFanRefinedRoutes_strictlyAvoidEachOther
    firstDirection secondDirection first second
    (valid.2.1 first second firstDirection secondDirection
      slotsLt firstDirectionEq secondDirectionEq)
    slotsLt

end PeriodicEightOccurrenceSplit
end LeanTrominoes
