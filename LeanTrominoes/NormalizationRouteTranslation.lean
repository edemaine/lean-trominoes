/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRoutes
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionTranslation

/-! # Translation commutes with each local vertex-normalization round -/
namespace LeanTrominoes.PeriodicThreeDM
open PeriodicOrthocrossing

@[simp] theorem normalizeVertexPosition_add (offset position : Cell) :
    normalizeVertexPosition (Cell.add offset position)=
      Cell.add (Cell.scale vertexNormalizationScale offset) (normalizeVertexPosition position) := by
  apply Prod.ext <;> simp [normalizeVertexPosition,Cell.add,Cell.scale] <;> ring

theorem normalizationTemplateAt_add (offset position : Cell) (points : List Cell) :
    normalizationTemplateAt (Cell.add offset position) points=
      translatePolyline (Cell.scale vertexNormalizationScale offset) (normalizationTemplateAt position points) := by
  simp only [normalizationTemplateAt,translatePolyline,List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp [Cell.add,Cell.scale] <;> ring

theorem magnifiedUnitRoute_translate (offset : Cell) (points : List Cell) :
    magnifiedUnitRoute (translatePolyline offset points)=
      translatePolyline (Cell.scale vertexNormalizationScale offset) (magnifiedUnitRoute points) := by
  have mapped : (translatePolyline offset points).map normalizeVertexPosition=
      (points.map normalizeVertexPosition).map (Cell.add (Cell.scale vertexNormalizationScale offset)) := by
    simp only [translatePolyline,List.map_map]
    apply List.map_congr_left
    intro point _
    exact normalizeVertexPosition_add offset point
  unfold magnifiedUnitRoute
  rw [mapped,AxisDirection.unitSubdividePolyline_map_add]
  rfl

theorem trimmedMagnifiedRoute_translate (offset : Cell) (points : List Cell) :
    trimmedMagnifiedRoute (translatePolyline offset points)=
      translatePolyline (Cell.scale vertexNormalizationScale offset) (trimmedMagnifiedRoute points) := by
  unfold trimmedMagnifiedRoute
  rw [magnifiedUnitRoute_translate]
  simp [translatePolyline]

/-- All coordinate dependence in one round is affine; template choices are
unchanged by translating the incoming drawing. -/
theorem normalizeRouteWithTemplates_translate (offset source target : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell) :
    normalizeRouteWithTemplates (Cell.add offset source) (Cell.add offset target)
      sourceTemplate targetTemplate (translatePolyline offset oldRoute)=
    translatePolyline (Cell.scale vertexNormalizationScale offset)
      (normalizeRouteWithTemplates source target sourceTemplate targetTemplate oldRoute) := by
  unfold normalizeRouteWithTemplates
  rw [normalizationTemplateAt_add,normalizationTemplateAt_add,trimmedMagnifiedRoute_translate]
  simp [translatePolyline,joinAtEndpoint]
end LeanTrominoes.PeriodicThreeDM
