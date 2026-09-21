/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticQuantifiers

/-! # Correctness of the compiled drawing planarity program -/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open BoundedArithmetic BoundedArithmetic.Expr PeriodicOrthocrossing

private theorem box_coordinates (r : Nat) (p : Cell) (h : FiniteBounds.InBox r p) :
    ∃ x<2*r+1, ∃ y<2*r+1, p=((x:Int)-(r:Int),(y:Int)-(r:Int)) := by
  rcases p with ⟨px,py⟩
  rcases h with ⟨hx,hx',hy,hy'⟩
  refine ⟨(px+r).toNat,by omega,(py+r).toNat,by omega,?_⟩
  apply Prod.ext <;> simp only [Prod.fst,Prod.snd] <;> omega

private theorem relative_coordinates (d : PeriodicGridDrawing) (t : Cell)
    (h : t ∈ FiniteBounds.translations (2*FiniteBounds.radius d)) :
    ∃ x<4*FiniteBounds.radius d+1, ∃ y<4*FiniteBounds.radius d+1, t=relative d x y := by
  obtain ⟨x,hx,y,hy,eq⟩ := box_coordinates (2*FiniteBounds.radius d) t ((FiniteBounds.mem_translations _ _).mp h)
  exact ⟨x,by omega,y,by omega,by simpa [relative] using eq⟩

private theorem contains_box (r : Nat) (s : GridSegment) (p : Cell)
    (hs : FiniteBounds.InBox r s.start ∧ FiniteBounds.InBox r s.finish) (hp : s.Contains p) :
    FiniteBounds.InBox r p := by
  simp only [FiniteBounds.InBox,GridSegment.Contains,GridSegment.IsHorizontal,GridSegment.IsVertical,
    GridSegment.Between] at *
  omega

theorem bounded_implies_planar (d : PeriodicGridDrawing)
    (routes : RoutesBounded d) (vertices : VerticesBounded d) (continuous : ContinuousBounded d) :
    d.IsContinuouslyPlanar := by
  apply (FiniteBounds.check_correct d).mp
  simp only [FiniteBounds.check,Bool.and_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · simp only [FiniteBounds.routeCheck,List.all_eq_true,decide_eq_true_eq]
    intro a ha b hb t ht p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hb
    obtain ⟨x,hx,y,hy,rfl⟩ := relative_coordinates d t ht
    by_cases contact : d.indexedSegments[j].segment.Contains p
    · have box := contains_box (FiniteBounds.radius d) d.indexedSegments[j].segment p
        (FiniteBounds.segment_bounds d _ (List.getElem_mem hj)) contact
      obtain ⟨px,hpx,py,hpy,eq⟩ := box_coordinates (FiniteBounds.radius d) p box
      have interior := (mem_segmentInteriorPoints_iff _ _).mp hp
      have tested := routes i hi j hj x hx y hy px hpx py hpy
      change p=point d px py at eq
      rw [← eq] at tested
      rcases tested with same | no
      · exact Or.inl same
      · exact (no ⟨interior,contact⟩).elim
    · exact Or.inr contact
  · simp only [FiniteBounds.vertexCheck,List.all_eq_true,decide_eq_true_eq]
    intro v hv a ha t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨x,hx,y,hy,rfl⟩ := relative_coordinates d t ht
    exact vertices i hi j hj x hx y hy
  · simp only [FiniteBounds.continuousCheck,List.all_eq_true,decide_eq_true_eq]
    intro a ha b hb t ht
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hb
    obtain ⟨x,hx,y,hy,rfl⟩ := relative_coordinates d t ht
    exact continuous i hi j hj x hx y hy

theorem planar_implies_bounded (d : PeriodicGridDrawing) (h : d.IsContinuouslyPlanar) :
    RoutesBounded d ∧ VerticesBounded d ∧ ContinuousBounded d := by
  refine ⟨?_,?_,?_⟩
  · intro a ha b hb x _ y _ px _ py _
    by_cases same : SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0)
    · exact Or.inl same
    · right
      rintro ⟨first,second⟩
      apply h.1.1 _ (List.getElem_mem ha) _ (List.getElem_mem hb) (relative d x y) (0,0) (point d px py) same first
      simpa [GridSegment.translate,periodTranslation,Cell.scale,Cell.add] using second
  · intro v hv a ha x _ y _
    have avoid := h.1.2 _ (List.getElem_mem hv) _ (List.getElem_mem ha) (0,0) (relative d x y)
    simpa [periodTranslation,Cell.scale,Cell.add] using avoid
  · intro a ha b hb x _ y _
    by_cases same : SegmentOccurrenceKey d.indexedSegments[a] (relative d x y) = SegmentOccurrenceKey d.indexedSegments[b] (0,0)
    · exact Or.inl same
    · right
      have avoid := h.2 _ (List.getElem_mem ha) _ (List.getElem_mem hb) (relative d x y) (0,0) same
      simpa [GridSegment.translate,periodTranslation,Cell.scale,Cell.add] using avoid

theorem predicate_correct (d : PeriodicGridDrawing) : predicate.Truth (fields d) ↔ d.IsContinuouslyPlanar := by
  rw [predicate,truth_and,truth_and,routePredicate_truth,vertexPredicate_truth,continuousPredicate_truth]
  exact ⟨fun h => bounded_implies_planar d h.1 h.2.1 h.2.2,planar_implies_bounded d⟩

theorem decision_eval (d : PeriodicGridDrawing) :
    decision.eval (fields d) = (FiniteBounds.check d).toNat := by
  have correct := predicate_correct d
  rw [← FiniteBounds.check_correct] at correct
  by_cases zero : predicate.eval (fields d)=0
  · have : FiniteBounds.check d=false := by
      cases he : FiniteBounds.check d
      · rfl
      · exact False.elim ((correct.mpr he) zero)
    simp [decision,Expr.eval,zero,this]
  · have : FiniteBounds.check d=true := correct.mp zero
    simp [decision,Expr.eval,zero,this]

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
