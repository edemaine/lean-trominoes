/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMEdgeIndices
import LeanTrominoes.PeriodicThreeDMFiniteDrawingCertificate
import Mathlib.Data.List.Enum

/-! # Route compatibility at the explicit three-incidences-per-triple indices -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget FieldQueries PeriodicGridDrawing

def IndexedRouteMatch (p : PeriodicThreeDM) (d : PeriodicGridDrawing) (i : Nat) (color : WireColor) : Prop :=
  let reference := (p.triples.getD i default).reference color
  let route := d.edgeRoute (3*i+colorIndex color)
  route.head? = some (d.vertexPositions.getD i (0,0)) ∧
    route.getLast? = some (Cell.add (d.vertexPositions.getD (p.elementVertexIndex color reference.atom) (0,0))
      (d.periodTranslation reference.offset))

theorem routesMatchCheck_iff_indexed (p : PeriodicThreeDM) (d : PeriodicGridDrawing) (wf : p.IsWellFormed) :
    FiniteDrawingCertificate.routesMatchCheck p d = true ↔
      ∀ i < p.triples.length, ∀ color, IndexedRouteMatch p d i color := by
  simp only [FiniteDrawingCertificate.routesMatchCheck,List.all_eq_true,decide_eq_true_eq,List.forall_mem_zipIdx']
  have atIndex (i : Nat) (hi : i<p.triples.length) (color : WireColor) :
      (d.edgeRoute (3*i+colorIndex color)).head? =
        some (d.vertexPosition p.incidenceGraph (p.incidenceGraph.edges[3*i+colorIndex color]'(edgeIndex_lt p i hi color)).source) ∧
      (d.edgeRoute (3*i+colorIndex color)).getLast? =
        some (Cell.add (d.vertexPosition p.incidenceGraph (p.incidenceGraph.edges[3*i+colorIndex color]'(edgeIndex_lt p i hi color)).target)
          (d.periodTranslation (p.incidenceGraph.edges[3*i+colorIndex color]'(edgeIndex_lt p i hi color)).offset)) ↔
      IndexedRouteMatch p d i color := by
    have ha := wf p.triples[i] (List.getElem_mem hi) color
    simp only [incidence_edge_at p i hi color,incidenceEdge,vertexPosition,tripleVertex_idxOf p i hi,
      elementVertex_idxOf p color _ ha,IndexedRouteMatch,List.getD_eq_getElem _ _ hi]
  constructor
  · intro h i hi color
    exact (atIndex i hi color).mp (h _ (edgeIndex_lt p i hi color))
  · intro h k hk
    obtain ⟨i,hi,color,rfl⟩ := edgeIndex_coordinates p k hk
    exact (atIndex i hi color).mpr (h i hi color)

end LeanTrominoes.PeriodicThreeDM
