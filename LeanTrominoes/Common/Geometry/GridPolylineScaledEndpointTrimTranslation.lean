/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineScaledEndpointTrim
import LeanTrominoes.Graphs.Drawings.Orthogonal.OrthogonalPolylineEndpointDirections

/-! # Endpoint trimming commutes with periodic translation -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem clippedScaledPoint_translate (route : List Cell) (offset : Cell) (index : Nat) (point : Cell) :
    clippedScaledPoint (translatePolyline offset route) index (Cell.add offset point) =
      Cell.add (Cell.scale 32 offset) (clippedScaledPoint route index point) := by
  by_cases first : index = 0
  · simp only [clippedScaledPoint,first,ite_true,translatePolyline,List.getElem?_map,Option.getD_map,
      AxisDirection.between_add_left]
    apply Prod.ext <;> simp only [Cell.add,Cell.scale,Prod.fst,Prod.snd] <;> ring
  · by_cases last : index+1 = route.length
    · simp only [clippedScaledPoint,first,ite_false,translatePolyline,List.length_map,last,ite_true,
        List.getElem?_map,Option.getD_map,AxisDirection.between_add_left]
      apply Prod.ext <;> simp only [Cell.add,Cell.scale,Prod.fst,Prod.snd] <;> ring
    · simp only [clippedScaledPoint,first,ite_false,translatePolyline,List.length_map,last]
      apply Prod.ext <;> simp only [Cell.add,Cell.scale,Prod.fst,Prod.snd] <;> ring

theorem clippedScaledRoute_translate (route : List Cell) (offset : Cell) :
    clippedScaledRoute (translatePolyline offset route) =
      translatePolyline (Cell.scale 32 offset) (clippedScaledRoute route) := by
  apply List.ext_getElem?
  intro index
  simp only [clippedScaledRoute,translatePolyline,List.getElem?_mapIdx,List.getElem?_map,Option.map_map]
  cases found : route[index]? with
  | none => rfl
  | some point =>
    simp only [Option.map_some,Option.some.injEq]
    exact clippedScaledPoint_translate route offset index point

end LeanTrominoes.GridPolyline
