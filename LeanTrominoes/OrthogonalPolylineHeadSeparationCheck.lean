/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineStrictSeparationCheck
import LeanTrominoes.OrthogonalPolylineSegmentBoxCheck
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

namespace LeanTrominoes.PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Boolean check of listed contacts at the two route heads. -/
def routesMeetOnlyAtHeadsCheck (first second : List Cell) : Bool :=
  first.all fun a => second.all fun b => guardedCheck (a = b)
    (decide (first.head? = some a ∧ second.head? = some b))

@[simp]
theorem routesMeetOnlyAtHeadsCheck_eq_true (first second : List Cell) :
    routesMeetOnlyAtHeadsCheck first second = true ↔ RoutesMeetOnlyAtHeads first second := by
  simp [routesMeetOnlyAtHeadsCheck, RoutesMeetOnlyAtHeads, List.all_eq_true]

/-- Separate long tails by boxes, checking shared-head contact only on the
first segment of each route. -/
def routesAvoidAtHeadsCheck : List Cell → List Cell → Bool
  | a :: b :: rest, c :: d :: rest' =>
      routesAvoidEachOtherCheck [a, b] [c, d] &&
        routesMeetOnlyAtHeadsCheck [a, b] [c, d] &&
        segmentBoxesSeparateCheck (b :: rest) [c, d] &&
        segmentBoxesSeparateCheck [a, b] (d :: rest') &&
        segmentBoxesSeparateCheck (b :: rest) (d :: rest')
  | _, _ => false

/-- The fast shared-head check proves the original continuous and listed
contact predicates for the entire routes. -/
theorem routesAvoidAtHeadsCheck_sound (first second : List Cell)
    (checked : routesAvoidAtHeadsCheck first second = true) :
    RoutesAvoidEachOther first second ∧ RoutesMeetOnlyAtHeads first second := by
  cases first with
  | nil => simp [routesAvoidAtHeadsCheck] at checked
  | cons a first =>
    cases first with
    | nil => simp [routesAvoidAtHeadsCheck] at checked
    | cons b rest =>
      cases second with
      | nil => simp [routesAvoidAtHeadsCheck] at checked
      | cons c second =>
        cases second with
        | nil => simp [routesAvoidAtHeadsCheck] at checked
        | cons d rest' =>
          simp only [routesAvoidAtHeadsCheck, Bool.and_eq_true,
            routesAvoidEachOtherCheck_eq_true, routesMeetOnlyAtHeadsCheck_eq_true] at checked
          rcases checked with ⟨⟨⟨⟨prefixAvoid, prefixHeads⟩, tailPrefix⟩, prefixTail⟩, tailTail⟩
          have tailPrefixAvoid := routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _ tailPrefix
          have prefixTailAvoid := routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _ prefixTail
          have tailTailAvoid := routesStrictlyAvoidEachOther_of_segmentBoxesCheck _ _ tailTail
          have joinedFirst := prefixAvoid.join_left_of_head_contact prefixHeads tailPrefixAvoid rfl rfl
          have joinedFirstTail := prefixTailAvoid.join_left tailTailAvoid rfl rfl
          have secondPrefixAvoid : RoutesAvoidEachOther [c, d] (a :: b :: rest) :=
            routesAvoidEachOther_comm joinedFirst.1
          have joinedSecond := secondPrefixAvoid.join_left_of_head_contact
            joinedFirst.2.symm joinedFirstTail.symm rfl rfl
          exact ⟨routesAvoidEachOther_comm joinedSecond.1, joinedSecond.2.symm⟩

end LeanTrominoes.PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
