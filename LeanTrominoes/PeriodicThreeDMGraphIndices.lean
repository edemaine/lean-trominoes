/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMGraph
import LeanTrominoes.PeriodicThreeDMFieldQueries

/-! # Closed native indices of the periodic 3DM incidence vertices -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

def colorPrefix (p : PeriodicThreeDM) : WireColor → Nat
  | .red => 0
  | .green => p.redCount
  | .blue => p.redCount+p.greenCount

def elementVertexIndex (p : PeriodicThreeDM) (color : WireColor) (atom : Nat) : Nat :=
  p.triples.length+p.colorPrefix color+atom

theorem incidence_vertices_length (p : PeriodicThreeDM) :
    p.incidenceGraph.vertices.length = p.triples.length+p.redCount+p.greenCount+p.blueCount := by
  simp [incidenceGraph,tripleVertices,elementVertices,coloredElementVertices,elementCount,Nat.add_assoc]

theorem elementVertexIndex_lt (p : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (ha : atom < p.elementCount color) : p.elementVertexIndex color atom < p.incidenceGraph.vertices.length := by
  rw [incidence_vertices_length]
  cases color <;> simp only [elementVertexIndex,colorPrefix,elementCount] at * <;> omega

private theorem getD_map_range {A : Type} (f : Nat → A) (n i : Nat) (hi : i<n) (fallback : A) :
    ((List.range n).map f).getD i fallback = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem tripleVertex_getD (p : PeriodicThreeDM) (i : Nat) (hi : i<p.triples.length) :
    p.incidenceGraph.vertices.getD i (.triple 0) = .triple i := by
  change (p.tripleVertices++p.elementVertices).getD i (.triple 0) = _
  rw [List.getD_append _ _ _ _ (by simpa [tripleVertices] using hi)]
  exact getD_map_range _ _ _ hi _

theorem elementVertex_getD (p : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (ha : atom < p.elementCount color) :
    p.incidenceGraph.vertices.getD (p.elementVertexIndex color atom) (.triple 0) = .element color atom := by
  change (p.tripleVertices++p.elementVertices).getD (p.triples.length+p.colorPrefix color+atom) (.triple 0) = _
  rw [List.getD_append_right _ _ _ _ (by simp only [tripleVertices,List.length_map,List.length_range]; omega)]
  simp only [tripleVertices,List.length_map,List.length_range,
    show p.triples.length+p.colorPrefix color+atom-p.triples.length = p.colorPrefix color+atom by omega]
  change ((p.coloredElementVertices .red++p.coloredElementVertices .green)++p.coloredElementVertices .blue).getD
    (p.colorPrefix color+atom) (.triple 0) = _
  cases color with
  | red =>
    change atom < p.redCount at ha
    simp only [colorPrefix,Nat.zero_add]
    rw [List.getD_append _ _ _ _ (by simp [coloredElementVertices,elementCount]; omega)]
    rw [List.getD_append _ _ _ _ (by simpa [coloredElementVertices,elementCount] using ha)]
    exact getD_map_range _ _ _ ha _
  | green =>
    change atom < p.greenCount at ha
    simp only [colorPrefix]
    rw [List.getD_append _ _ _ _ (by simp [coloredElementVertices,elementCount]; omega)]
    rw [List.getD_append_right _ _ _ _ (by simp [coloredElementVertices,elementCount])]
    simp only [coloredElementVertices,List.length_map,List.length_range,elementCount,Nat.add_sub_cancel_left]
    exact getD_map_range _ _ _ ha _
  | blue =>
    change atom < p.blueCount at ha
    simp only [colorPrefix]
    rw [List.getD_append_right _ _ _ _ (by simp [coloredElementVertices,elementCount])]
    simp only [List.length_append,coloredElementVertices,List.length_map,List.length_range,elementCount,Nat.add_sub_cancel_left]
    exact getD_map_range _ _ _ ha _

theorem tripleVertex_idxOf (p : PeriodicThreeDM) (i : Nat) (hi : i<p.triples.length) :
    p.incidenceGraph.vertices.idxOf (.triple i) = i := by
  have bound : i<p.incidenceGraph.vertices.length := by rw [incidence_vertices_length]; omega
  have entry := tripleVertex_getD p i hi
  rw [List.getD_eq_getElem _ _ bound] at entry
  rw [← entry]
  exact p.incidenceGraph_vertices_nodup.idxOf_getElem i bound

theorem elementVertex_idxOf (p : PeriodicThreeDM) (color : WireColor) (atom : Nat)
    (ha : atom<p.elementCount color) :
    p.incidenceGraph.vertices.idxOf (.element color atom) = p.elementVertexIndex color atom := by
  have bound := elementVertexIndex_lt p color atom ha
  have entry := elementVertex_getD p color atom ha
  rw [List.getD_eq_getElem _ _ bound] at entry
  rw [← entry]
  exact p.incidenceGraph_vertices_nodup.idxOf_getElem _ bound

end LeanTrominoes.PeriodicThreeDM
