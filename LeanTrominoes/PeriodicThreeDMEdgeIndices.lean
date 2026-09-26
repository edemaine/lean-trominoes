/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMGraphIndices

/-! # Closed native indices of the three incidence edges per triple -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget FieldQueries

theorem incidence_edges_length (p : PeriodicThreeDM) : p.incidenceGraph.edges.length = 3*p.triples.length := by
  rw [incidenceGraph_edges_length,incidenceTags_eq_range_flatMap]
  simp [List.length_flatMap,tripleIncidenceTags,incidenceColors,Nat.mul_comm]

theorem colorIndex_lt (color : WireColor) : colorIndex color < 3 := by cases color <;> decide

theorem edgeIndex_lt (p : PeriodicThreeDM) (i : Nat) (hi : i<p.triples.length) (color : WireColor) :
    3*i+colorIndex color < p.incidenceGraph.edges.length := by
  rw [incidence_edges_length]
  have h := colorIndex_lt color
  omega

private theorem tag_get (indices : List Nat) (i : Nat) (hi : i < indices.length) (color : WireColor) :
    (indices.flatMap tripleIncidenceTags).getD (3*i+colorIndex color) ⟨0,.red⟩ = ⟨indices[i],color⟩ := by
  induction indices generalizing i with
  | nil => simp at hi
  | cons j rest ih =>
    cases i with
    | zero => cases color <;> simp [tripleIncidenceTags,incidenceColors,colorIndex]
    | succ i =>
      have address : 3*(i+1)+colorIndex color = (3*i+colorIndex color)+1+1+1 := by omega
      simpa [tripleIncidenceTags,incidenceColors,address] using ih i (by simpa using hi)

theorem incidence_edge_at (p : PeriodicThreeDM) (i : Nat) (hi : i<p.triples.length) (color : WireColor) :
    p.incidenceGraph.edges[3*i+colorIndex color]'(edgeIndex_lt p i hi color) =
      incidenceEdge i p.triples[i] color := by
  have tagAt := tag_get (List.range p.triples.length) i (by simpa using hi) color
  have tagsBound : 3*i+colorIndex color < p.incidenceTags.length := by
    rw [← incidenceGraph_edges_length]
    exact edgeIndex_lt p i hi color
  rw [← incidenceTags_eq_range_flatMap p,List.getD_eq_getElem _ _ tagsBound] at tagAt
  simp only [List.getElem_range] at tagAt
  simp only [incidenceGraph_edges_eq_tags_map,List.getElem_map,tagAt]
  simp only [incidenceEdgeAt,List.getD_eq_getElem _ _ hi]

theorem edgeIndex_coordinates (p : PeriodicThreeDM) (k : Nat) (hk : k<p.incidenceGraph.edges.length) :
    ∃ i < p.triples.length, ∃ color, k=3*i+colorIndex color := by
  rw [incidence_edges_length] at hk
  have bound : k/3<p.triples.length := by omega
  have hm := Nat.mod_lt k (by decide : 0<3)
  refine ⟨k/3,bound,?_⟩
  interval_cases he : k%3
  · exact ⟨.red,by simp only [colorIndex]; omega⟩
  · exact ⟨.green,by simp only [colorIndex]; omega⟩
  · exact ⟨.blue,by simp only [colorIndex]; omega⟩

end LeanTrominoes.PeriodicThreeDM
