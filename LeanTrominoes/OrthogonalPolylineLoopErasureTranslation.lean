/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation
import LeanTrominoes.OrthogonalPolylineSymmetries

/-!
# Translation equivariance of orthogonal loop erasure

The walk `bypass` algorithm depends only on equality among visited vertices.
Consequently it commutes with every injective graph map.  Specializing this
fact to integer translations proves that the total orthogonal polyline
normalizer commutes with translation.
-/

namespace SimpleGraph
namespace Walk

/-- Dropping a walk through the first occurrence of a vertex commutes with
an injective graph homomorphism. -/
theorem dropUntil_map_of_injective
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq V] [DecidableEq W]
    (f : G →g H) (injective : Function.Injective f)
    {source target : V} (walk : G.Walk source target)
    (vertex : V) (member : vertex ∈ walk.support) :
    (walk.map f).dropUntil (f vertex) (by
        simpa only [support_map] using
          (List.mem_map.mpr ⟨vertex, member, rfl⟩)) =
      (walk.dropUntil vertex member).map f := by
  induction walk generalizing vertex with
  | nil =>
      have vertexEqual := mem_support_nil_iff.mp member
      subst vertex
      rfl
  | @cons source middle target adjacent tail induction =>
      by_cases sourceEqual : source = vertex
      · subst vertex
        simp [dropUntil]
      · have imagesDifferent : f source ≠ f vertex :=
          fun equal => sourceEqual (injective equal)
        simp only [map_cons, dropUntil,
          dif_neg sourceEqual, dif_neg imagesDifferent]
        apply induction

/-- Walk bypass commutes with every injective graph homomorphism. -/
theorem bypass_map_of_injective
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableEq V] [DecidableEq W]
    (f : G →g H) (injective : Function.Injective f)
    {source target : V} (walk : G.Walk source target) :
    (walk.map f).bypass = walk.bypass.map f := by
  induction walk with
  | nil => rfl
  | @cons source middle target adjacent tail induction =>
      simp only [map_cons, bypass, induction]
      by_cases sourceMember : source ∈ tail.bypass.support
      · have imageMember :
            f source ∈ (tail.bypass.map f).support := by
          simp only [support_map]
          exact List.mem_map.mpr ⟨source, sourceMember, rfl⟩
        rw [dif_pos sourceMember, dif_pos imageMember]
        exact dropUntil_map_of_injective
          f injective tail.bypass source sourceMember
      · have imageNotMember :
            f source ∉ (tail.bypass.map f).support := by
          simp only [support_map, List.mem_map]
          rintro ⟨vertex, vertexMember, imageEqual⟩
          exact sourceMember ((injective imageEqual).symm ▸ vertexMember)
        rw [dif_neg sourceMember, dif_neg imageNotMember]
        rfl

end Walk
end SimpleGraph

namespace LeanTrominoes
namespace AxisDirection

/-- Translation is an automorphism of the unit-axis grid graph. -/
def unitAxisTranslationHom (offset : Cell) :
    unitAxisGraph →g unitAxisGraph where
  toFun := Cell.add offset
  map_rel' := by
    intro first second adjacent
    rw [unitAxisGraph_adj_iff] at adjacent ⊢
    rcases adjacent with ⟨direction, genuine, rfl⟩
    refine ⟨direction, genuine, ?_⟩
    rcases offset with ⟨offsetX, offsetY⟩
    rcases first with ⟨firstX, firstY⟩
    cases direction <;>
      simp [step, Cell.add] <;>
      ring

theorem unitAxisTranslationHom_injective (offset : Cell) :
    Function.Injective (unitAxisTranslationHom offset) :=
  Cell.add_left_injective offset

/-- Translating an orthogonal route before loop erasure translates the
resulting simple unit path pointwise. -/
theorem eraseOrthogonalLoops_map_add
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (offset : Cell) :
    eraseOrthogonalLoops
        (points.map (Cell.add offset))
        (by simpa using nonempty)
        (orthogonal.translate offset) =
      (eraseOrthogonalLoops points nonempty orthogonal).map
        (Cell.add offset) := by
  let translatedPoints := points.map (Cell.add offset)
  have translatedNonempty : translatedPoints ≠ [] := by
    simpa [translatedPoints] using nonempty
  let translatedOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline translatedPoints :=
    orthogonal.translate offset
  let originalWalk :=
    orthogonalUnitWalk nonempty orthogonal
  let translatedWalk :=
    orthogonalUnitWalk translatedNonempty translatedOrthogonal
  let mappedWalk :=
    originalWalk.map (unitAxisTranslationHom offset)
  have startEqual :
      Cell.add offset
          ((unitSubdividePolyline points).head
            (unitSubdividePolyline_ne_nil nonempty)) =
        (unitSubdividePolyline translatedPoints).head
          (unitSubdividePolyline_ne_nil translatedNonempty) := by
    simp [translatedPoints, unitSubdividePolyline_map_add]
  have finishEqual :
      Cell.add offset
          ((unitSubdividePolyline points).getLast
            (unitSubdividePolyline_ne_nil nonempty)) =
        (unitSubdividePolyline translatedPoints).getLast
          (unitSubdividePolyline_ne_nil translatedNonempty) := by
    simp [translatedPoints, unitSubdividePolyline_map_add]
  have walksEqual :
      mappedWalk.copy startEqual finishEqual = translatedWalk := by
    apply SimpleGraph.Walk.ext_support
    simp [mappedWalk, originalWalk, translatedWalk,
      orthogonalUnitWalk, translatedPoints,
      unitSubdividePolyline_map_add, unitAxisTranslationHom]
  change translatedWalk.bypass.support =
    originalWalk.bypass.support.map (Cell.add offset)
  rw [← walksEqual, SimpleGraph.Walk.bypass_copy,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.bypass_map_of_injective
      (unitAxisTranslationHom offset)
      (unitAxisTranslationHom_injective offset) originalWalk,
    SimpleGraph.Walk.support_map]
  rfl

/-- The total orthogonal-route normalizer commutes with an integer
translation on every nonempty orthogonal input. -/
theorem normalizeOrthogonalPolyline_map_add
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (offset : Cell) :
    normalizeOrthogonalPolyline
        (points.map (Cell.add offset)) =
      (normalizeOrthogonalPolyline points).map
        (Cell.add offset) := by
  have translatedNonempty :
      points.map (Cell.add offset) ≠ [] := by
    simpa using nonempty
  have translatedOrthogonal := orthogonal.translate offset
  rw [normalizeOrthogonalPolyline_eq_erase
      translatedNonempty translatedOrthogonal,
    normalizeOrthogonalPolyline_eq_erase nonempty orthogonal]
  exact eraseOrthogonalLoops_map_add
    nonempty orthogonal offset

end AxisDirection
end LeanTrominoes
