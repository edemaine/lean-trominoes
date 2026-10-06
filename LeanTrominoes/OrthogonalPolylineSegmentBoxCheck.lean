/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.FiniteBoolCheck

namespace LeanTrominoes

private def segmentLower (s : GridSegment) : Cell :=
  (min s.start.1 s.finish.1, min s.start.2 s.finish.2)
private def segmentUpper (s : GridSegment) : Cell :=
  (max s.start.1 s.finish.1, max s.start.2 s.finish.2)

private theorem segment_start_bounded (s : GridSegment) :
    InClosedGridRectangle (segmentLower s) (segmentUpper s) s.start := by
  simp [InClosedGridRectangle, segmentLower, segmentUpper]
private theorem segment_finish_bounded (s : GridSegment) :
    InClosedGridRectangle (segmentLower s) (segmentUpper s) s.finish := by
  simp [InClosedGridRectangle, segmentLower, segmentUpper]

private abbrev Box := Cell × Cell

private def boxContains (outer inner : Box) : Prop :=
  outer.1.1 ≤ inner.1.1 ∧ outer.1.2 ≤ inner.1.2 ∧
    inner.2.1 ≤ outer.2.1 ∧ inner.2.2 ≤ outer.2.2

private def joinBoxes (a b : Box) : Box :=
  ((min a.1.1 b.1.1, min a.1.2 b.1.2),
    (max a.2.1 b.2.1, max a.2.2 b.2.2))

private theorem joinBoxes_contains_left (a b : Box) : boxContains (joinBoxes a b) a := by
  simp [boxContains, joinBoxes]
private theorem joinBoxes_contains_right (a b : Box) : boxContains (joinBoxes a b) b := by
  simp [boxContains, joinBoxes]
private theorem boxContains_trans {a b c : Box}
    (ab : boxContains a b) (bc : boxContains b c) : boxContains a c := by
  simp only [boxContains] at *
  omega

private def boxesHull : List Box → Box
  | [] => ((0, 0), (0, 0))
  | [a] => a
  | a :: b :: rest => joinBoxes a (boxesHull (b :: rest))

private theorem boxesHull_contains {boxes : List Box} {box : Box}
    (member : box ∈ boxes) : boxContains (boxesHull boxes) box := by
  induction boxes with
  | nil => simp at member
  | cons a rest ih =>
    cases rest with
    | nil =>
        have eq : box = a := by simpa using member
        subst box
        simp [boxesHull, boxContains]
    | cons b rest =>
      rcases List.mem_cons.mp member with rfl | member
      · exact joinBoxes_contains_left _ _
      · exact boxContains_trans (joinBoxes_contains_right _ _) (ih member)

private theorem separated_of_boxContains {a b outerA outerB : Box}
    (containedA : boxContains outerA a) (containedB : boxContains outerB b)
    (separated : ClosedGridRectanglesSeparated outerA.1 outerA.2 outerB.1 outerB.2) :
    ClosedGridRectanglesSeparated a.1 a.2 b.1 b.2 := by
  simp only [boxContains] at containedA containedB
  simp only [ClosedGridRectanglesSeparated] at *
  omega

private def boxChunksAux : Nat → List Box → List (List Box)
  | 0, boxes => [boxes]
  | _ + 1, [] => []
  | fuel + 1, boxes@(_ :: _) =>
      boxes.take 8 :: boxChunksAux fuel (boxes.drop 8)

private theorem boxChunksAux_flatten (fuel : Nat) (boxes : List Box) :
    (boxChunksAux fuel boxes).flatten = boxes := by
  induction fuel generalizing boxes with
  | zero => simp [boxChunksAux]
  | succ fuel ih =>
      cases boxes with
      | nil => rfl
      | cons a rest => simp [boxChunksAux, ih, List.take_append_drop]

/-- Skip whole blocks of segment pairs when their bounding boxes are disjoint. -/
private def chunkedBoxesCheck (first second : List Box) : Bool :=
  let firstChunks := (boxChunksAux first.length first).map fun block => (boxesHull block, block)
  let secondChunks := (boxChunksAux second.length second).map fun block => (boxesHull block, block)
  decide (ClosedGridRectanglesSeparated (boxesHull first).1 (boxesHull first).2
      (boxesHull second).1 (boxesHull second).2) ||
    firstChunks.all (fun a => secondChunks.all (fun b =>
    decide (ClosedGridRectanglesSeparated a.1.1 a.1.2 b.1.1 b.1.2) ||
      a.2.all (fun x => b.2.all (fun y =>
        decide (ClosedGridRectanglesSeparated x.1 x.2 y.1 y.2)))))

private theorem chunkedBoxesCheck_sound (first second : List Box)
    (checked : chunkedBoxesCheck first second = true) :
    ∀ a ∈ first, ∀ b ∈ second,
      ClosedGridRectanglesSeparated a.1 a.2 b.1 b.2 := by
  simp only [chunkedBoxesCheck, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Bool.or_eq_true,
    decide_eq_true_eq] at checked
  intro a ha b hb
  rcases checked with separated | checked
  · exact separated_of_boxContains (boxesHull_contains ha) (boxesHull_contains hb) separated
  · rw [← boxChunksAux_flatten first.length first] at ha
    rw [← boxChunksAux_flatten second.length second] at hb
    rcases List.mem_flatten.mp ha with ⟨as, has, ha⟩
    rcases List.mem_flatten.mp hb with ⟨bs, hbs, hb⟩
    rcases checked as has bs hbs with separated | separated
    · exact separated_of_boxContains (boxesHull_contains ha) (boxesHull_contains hb) separated
    · exact separated a ha b hb

/-- A sufficient strict-separation certificate using only closed segment boxes. -/
def segmentBoxesSeparateCheck (first second : List Cell) : Bool :=
  let firstBoxes := (gridPolylineSegments first).map fun s => (segmentLower s, segmentUpper s)
  let secondBoxes := (gridPolylineSegments second).map fun s => (segmentLower s, segmentUpper s)
  decide (2 ≤ first.length ∧ 2 ≤ second.length) &&
    chunkedBoxesCheck firstBoxes secondBoxes

/-- Separation of all closed segment boxes rules out every type of contact. -/
theorem routesStrictlyAvoidEachOther_of_segmentBoxesCheck
    (first second : List Cell)
    (checked : segmentBoxesSeparateCheck first second = true) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther first second := by
  simp only [segmentBoxesSeparateCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  rcases checked with ⟨⟨firstLength, secondLength⟩, checked⟩
  have separated := chunkedBoxesCheck_sound _ _ checked
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at separated
  have firstPointBounded (point : Cell) (member : point ∈ first) :
      ∃ segment ∈ gridPolylineSegments first,
        InClosedGridRectangle (segmentLower segment) (segmentUpper segment) point := by
    rcases exists_gridPolylineSegment_of_mem firstLength member with ⟨s, hs, eq⟩
    refine ⟨s, hs, ?_⟩
    rcases eq with rfl | rfl
    · exact segment_start_bounded s
    · exact segment_finish_bounded s
  have secondPointBounded (point : Cell) (member : point ∈ second) :
      ∃ segment ∈ gridPolylineSegments second,
        InClosedGridRectangle (segmentLower segment) (segmentUpper segment) point := by
    rcases exists_gridPolylineSegment_of_mem secondLength member with ⟨s, hs, eq⟩
    refine ⟨s, hs, ?_⟩
    rcases eq with rfl | rfl
    · exact segment_start_bounded s
    · exact segment_finish_bounded s
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact not_interiorsMeet_of_inClosedGridRectangles_of_separated
      (segment_start_bounded a) (segment_finish_bounded a)
      (segment_start_bounded b) (segment_finish_bounded b) (separated a ha b hb)
  · intro point hp b hb
    rcases firstPointBounded point hp with ⟨a, ha, bounded⟩
    exact not_interiorContains_of_inClosedGridRectangles_of_separated
      bounded (segment_start_bounded b) (segment_finish_bounded b) (separated a ha b hb)
  · intro point hp a ha
    rcases secondPointBounded point hp with ⟨b, hb, bounded⟩
    exact not_interiorContains_of_inClosedGridRectangles_of_separated
      bounded (segment_start_bounded a) (segment_finish_bounded a) (separated a ha b hb).symm
  · intro x hx y hy
    rcases firstPointBounded x hx with ⟨a, ha, boundedA⟩
    rcases secondPointBounded y hy with ⟨b, hb, boundedB⟩
    exact ne_of_inClosedGridRectangles_of_separated boundedA boundedB (separated a ha b hb)

end LeanTrominoes
