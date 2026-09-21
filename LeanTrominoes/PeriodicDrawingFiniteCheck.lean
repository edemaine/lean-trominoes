/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingFiniteBounds

/-! # A finite planarity checker without a bounding-box promise -/
namespace LeanTrominoes.PeriodicGridDrawing.FiniteBounds
open PeriodicOrthocrossing

def coordinates (r : Nat) : List Int := (List.range (2*r+1)).map (fun n : Nat => (n:Int)-(r:Int))
def translations (r : Nat) : List Cell :=
  (coordinates r).flatMap (fun x => (coordinates r).map (fun y => (x,y)))

@[simp] theorem mem_coordinates (r : Nat) (x : Int) :
    x ∈ coordinates r ↔ -(r:Int) ≤ x ∧ x ≤ r := by
  constructor
  · intro h
    obtain ⟨n,hn,eq⟩ := List.mem_map.mp h
    have bound := List.mem_range.mp hn
    omega
  · intro hx
    apply List.mem_map.mpr
    refine ⟨(x+(r:Int)).toNat,List.mem_range.mpr ?_,?_⟩ <;> omega

@[simp] theorem mem_translations (r : Nat) (p : Cell) : p ∈ translations r ↔ InBox r p := by
  rcases p with ⟨x,y⟩
  simp [translations,InBox,and_assoc]

def routeCheck (d : PeriodicGridDrawing) : Bool :=
  d.indexedSegments.all fun a => d.indexedSegments.all fun b =>
    (translations (2*radius d)).all fun t =>
      (segmentInteriorPoints (a.segment.translate (d.periodTranslation t))).all fun p =>
        decide (SegmentOccurrenceKey a t = SegmentOccurrenceKey b (0,0) ∨ ¬ b.segment.Contains p)

def vertexCheck (d : PeriodicGridDrawing) : Bool :=
  d.vertexPositions.all fun v => d.indexedSegments.all fun a =>
    (translations (2*radius d)).all fun t =>
      decide (¬ (a.segment.translate (d.periodTranslation t)).InteriorContains v)

def continuousCheck (d : PeriodicGridDrawing) : Bool :=
  d.indexedSegments.all fun a => d.indexedSegments.all fun b =>
    (translations (2*radius d)).all fun t =>
      decide (SegmentOccurrenceKey a t = SegmentOccurrenceKey b (0,0) ∨
        ¬ GridSegment.InteriorsMeet (a.segment.translate (d.periodTranslation t)) b.segment)

def check (d : PeriodicGridDrawing) : Bool := routeCheck d && vertexCheck d && continuousCheck d

theorem routes_of_check (d : PeriodicGridDrawing) (h : routeCheck d = true) : d.RoutesAvoidInteriors := by
  simp only [routeCheck,List.all_eq_true,decide_eq_true_eq,mem_translations] at h
  intro a ha b hb t u p ne first second
  let relative := Cell.sub t u
  let normalized := d.normalizePoint p u
  have first' : (a.segment.translate (d.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize d a.segment t u p).mp first
  have second' : b.segment.Contains normalized := by
    simpa [Cell.sub,periodTranslation,Cell.scale,GridSegment.translate,Cell.add] using
      (contains_normalize d b.segment u u p).mp second
  have bound := relative_bound d a.segment b.segment relative (segment_bounds d a ha)
    (segment_bounds d b hb) (rectangles_of_contact _ _ _ first' second')
  rcases h a ha b hb relative bound normalized ((mem_segmentInteriorPoints_iff _ _).mpr first') with eq | no
  · exact relative_key_ne ne eq
  · exact no second'

theorem vertices_of_check (d : PeriodicGridDrawing) (h : vertexCheck d = true) : d.VerticesAvoidRouteInteriors := by
  simp only [vertexCheck,List.all_eq_true,decide_eq_true_eq,mem_translations] at h
  intro v hv a ha t u contact
  let relative := Cell.sub u t
  have normalized : (a.segment.translate (d.periodTranslation relative)).InteriorContains v := by
    have := (interiorContains_normalize d a.segment u t (Cell.add v (d.periodTranslation t))).mp contact
    simpa [relative,normalizePoint,Cell.add,Cell.sub] using this
  have bounds := vertex_bound d v hv
  have bound := relative_bound d a.segment ⟨v,v⟩ relative (segment_bounds d a ha)
    ⟨bounds,bounds⟩ (rectangles_of_vertex _ _ normalized)
  exact h v hv a ha relative bound normalized

theorem continuous_of_check (d : PeriodicGridDrawing) (h : continuousCheck d = true) : d.RoutesHaveDisjointInteriors := by
  simp only [continuousCheck,List.all_eq_true,decide_eq_true_eq,mem_translations] at h
  intro a ha b hb t u ne meet
  let relative := Cell.sub t u
  have normalized := (interiorsMeet_normalize d a.segment b.segment t u).mp meet
  have bound := relative_bound d a.segment b.segment relative (segment_bounds d a ha)
    (segment_bounds d b hb) (rectangles_of_interiors _ _ normalized)
  rcases h a ha b hb relative bound with eq | no
  · exact relative_key_ne ne eq
  · exact no normalized

theorem check_of_planar (d : PeriodicGridDrawing) (h : d.IsContinuouslyPlanar) : check d = true := by
  simp only [check,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp only [routeCheck,List.all_eq_true,decide_eq_true_eq]
    intro a ha b hb t _ p hp
    by_cases eq : SegmentOccurrenceKey a t = SegmentOccurrenceKey b (0,0)
    · exact Or.inl eq
    · right
      intro contact
      apply h.1.1 a ha b hb t (0,0) p eq ((mem_segmentInteriorPoints_iff _ _).mp hp)
      simpa [GridSegment.translate,periodTranslation,Cell.scale,Cell.add] using contact
  · simp only [vertexCheck,List.all_eq_true,decide_eq_true_eq]
    intro v hv a ha t _
    have avoid := h.1.2 v hv a ha (0,0) t
    simpa [periodTranslation,Cell.scale,Cell.add] using avoid
  · simp only [continuousCheck,List.all_eq_true,decide_eq_true_eq]
    intro a ha b hb t _
    by_cases eq : SegmentOccurrenceKey a t = SegmentOccurrenceKey b (0,0)
    · exact Or.inl eq
    · right
      have avoid := h.2 a ha b hb t (0,0) eq
      simpa [GridSegment.translate,periodTranslation,Cell.scale,Cell.add] using avoid

/-- Exact finite checking, including arbitrarily distant stored representatives. -/
theorem check_correct (d : PeriodicGridDrawing) : check d = true ↔ d.IsContinuouslyPlanar := by
  constructor
  · intro h
    simp only [check,Bool.and_eq_true] at h
    exact ⟨⟨routes_of_check d h.1.1,vertices_of_check d h.1.2⟩,continuous_of_check d h.2⟩
  · exact check_of_planar d

def decidablePlanarity (d : PeriodicGridDrawing) : Decidable d.IsContinuouslyPlanar :=
  decidable_of_iff (check d = true) (check_correct d)

end LeanTrominoes.PeriodicGridDrawing.FiniteBounds
