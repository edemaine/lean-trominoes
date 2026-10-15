/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.Geometry.GridPolylineRealScaling

/-! # Endpoint containment under affine transformations -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem RealIsEndpoint.map {route : List Cell} {point : ℝ × ℝ}
    (endpoint : RealIsEndpoint route point) (function : Cell → Cell) (realFunction : ℝ × ℝ → ℝ × ℝ)
    (agrees : ∀ cell, realFunction (realCell cell) = realCell (function cell)) :
    RealIsEndpoint (route.map function) (realFunction point) := by
  rcases endpoint with ⟨cell,head,rfl⟩ | ⟨cell,last,rfl⟩
  · exact Or.inl ⟨function cell,by simp only [List.head?_map,head,Option.map_some],agrees cell⟩
  · exact Or.inr ⟨function cell,by simp only [List.getLast?_map,last,Option.map_some],agrees cell⟩

theorem RealIsEndpoint.translate {route : List Cell} {point : ℝ × ℝ}
    (endpoint : RealIsEndpoint route point) (offset : Cell) :
    RealIsEndpoint (translatePolyline offset route) (offset.1+point.1,offset.2+point.2) := by
  apply endpoint.map (Cell.add offset) (fun point => (offset.1+point.1,offset.2+point.2))
  intro cell
  simp [realCell,Cell.add]

theorem RealIsEndpoint.scale {route : List Cell} {point : ℝ × ℝ}
    (endpoint : RealIsEndpoint route point) (factor : Int) :
    RealIsEndpoint (scalePolyline factor route) ((factor : ℝ)*point.1,(factor : ℝ)*point.2) := by
  apply endpoint.map (Cell.scale factor) (fun point => ((factor : ℝ)*point.1,(factor : ℝ)*point.2))
  intro cell
  simp [realCell,Cell.scale]

end LeanTrominoes.GridPolyline
