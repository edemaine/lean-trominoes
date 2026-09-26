/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Data.List.GetD

/-! # Reconstructing the ordered vertex table through vertex lookup -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem vertexPositions_eq_map_vertexPosition {Vertex : Type*} [DecidableEq Vertex]
    (g : PeriodicGraph Vertex) (d : PeriodicGridDrawing)
    (distinct : g.vertices.Nodup) (length : d.vertexPositions.length = g.vertices.length) :
    d.vertexPositions = g.vertices.map (d.vertexPosition g) := by
  apply List.ext_getElem
  · simpa using length
  · intro i hi hj
    have bound : i < g.vertices.length := by simpa using hj
    simp only [List.getElem_map,vertexPosition,distinct.idxOf_getElem i bound]
    exact (List.getD_eq_getElem _ _ hi).symm

end LeanTrominoes.PeriodicGridDrawing
