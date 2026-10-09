/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendPerturbationVertexAvoidance

/-! # A planar periodic polygonal drawing with all bends off cell seams -/
namespace LeanTrominoes.PeriodicGridDrawing.InteriorBends

theorem perturbDrawing_planar {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 16*(drawing.gridSize:Int)+8<(factor:Int)) :
    (perturbDrawing drawing factor).IsRealPlanarDrawing source := by
  have gridPositive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have positive : 0<factor := by omega
  exact ⟨⟨perturbDrawing_compatible planar.1.1 positive,
    perturbDrawing_routesSimple planar localDrawing localGraph spacing,
    perturbDrawing_verticesAvoidRoutes planar localDrawing localGraph spacing⟩,
    perturbDrawing_routesMeetOnlyAtEndpoints planar localDrawing localGraph spacing⟩

theorem perturbDrawing_route_points_off_seams {drawing : PeriodicGridDrawing} {factor : Nat}
    (spacing : 2<(factor:Int)) {route : List Cell}
    (member : route∈(perturbDrawing drawing factor).edgeRoutes) {p : Cell} (pointMember : p∈route) :
    p.1%((perturbDrawing drawing factor).gridSize:Int)≠0 ∧
      p.2%((perturbDrawing drawing factor).gridSize:Int)≠0 := by
  have positive : 0<factor := by omega
  have gridPositive : (0:Int)<drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
  obtain ⟨oldPoint,_,rfl⟩ := List.mem_map.mp pointMember
  simp only [perturbDrawing_gridSize drawing positive,Nat.cast_mul,point]
  exact ⟨coordinate_off_seams gridPositive spacing,coordinate_off_seams gridPositive spacing⟩

end LeanTrominoes.PeriodicGridDrawing.InteriorBends
