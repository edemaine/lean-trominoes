/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Core.PeriodicGraphBendSubdivision
import LeanTrominoes.Graphs.Drawings.Refinement.Polygonal.PeriodicGridDrawingPolygonalPointBounds
import LeanTrominoes.Common.List.ListZipIdxStart

/-! # The finite graph and straight drawing obtained by inserting bend vertices -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def internalPoints (drawing : PeriodicGridDrawing) (index : Nat) : List (Cell × Nat) :=
  (drawing.edgeRoute index).tail.dropLast.zipIdx 1

def middle {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat)
    (tagged : PeriodicEdge V × Nat) : List (Vertex V × Cell) :=
  (internalPoints drawing tagged.2).map fun entry =>
    (.bend tagged.2 entry.2,InteriorBends.cell drawing.gridSize factor entry.1)

def subdivisionGraph {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing)
    (factor : Nat) : PeriodicGraph (Vertex V) :=
  graph source (middle drawing factor)

def position {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) : Vertex V → Cell
  | .original vertex => Cell.scale factor (drawing.vertexPosition source vertex)
  | .bend edgeIndex pointIndex => InteriorBends.representative drawing.gridSize factor
      ((drawing.edgeRoute edgeIndex).getD pointIndex (0,0))

def straightRoute {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (edge : PeriodicEdge (Vertex V)) : List Cell :=
  [position source drawing factor edge.source,
    Cell.add (position source drawing factor edge.target) (Cell.scale (factor*drawing.gridSize) edge.offset)]

def subdivisionDrawing {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) : PeriodicGridDrawing where
  gridSizePred := factor*drawing.gridSize-1
  vertexPositions := (subdivisionGraph source drawing factor).vertices.map (position source drawing factor)
  edgeRoutes := (subdivisionGraph source drawing factor).edges.map (straightRoute source drawing factor)

theorem subdivisionDrawing_gridSize {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) {factor : Nat} (positive : 0<factor) :
    (subdivisionDrawing source drawing factor).gridSize=factor*drawing.gridSize := by
  have gridPositive : 0<drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
  have periodPositive := Nat.mul_pos positive gridPositive
  change factor*drawing.gridSize-1+1=factor*drawing.gridSize
  omega

theorem middle_only_bends {V : Type*} (drawing : PeriodicGridDrawing) (factor : Nat)
    (edge : PeriodicEdge V × Nat) {entry : Vertex V × Cell} (member : entry∈middle drawing factor edge) :
    ∃ i j, entry.1=Vertex.bend i j := by
  obtain ⟨point,_,rfl⟩ := List.mem_map.mp member
  exact ⟨edge.2,point.2,rfl⟩

theorem middle_indices_unique {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor : Nat) :
    (source.edges.zipIdx.flatMap fun edge => (middle drawing factor edge).map Prod.fst).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro edge _
    have indices : ((internalPoints drawing edge.2).map Prod.snd).Nodup :=
      by
        have shifted := (List.nodup_zipIdx_map_snd (drawing.edgeRoute edge.2).tail.dropLast).map
          (fun a b (equal : a+1=b+1) => Nat.add_right_cancel equal)
        change (((drawing.edgeRoute edge.2).tail.dropLast.zipIdx 1).map Prod.snd).Nodup
        rw [list_zipIdx_start_eq _ 1]
        simpa only [List.map_map,Function.comp_def] using shifted
    have mapped := indices.map (f := fun index => (Vertex.bend edge.2 index : Vertex V))
      (fun i j equal => (Vertex.bend.inj equal).2)
    simpa only [middle,List.map_map,Function.comp_def] using mapped
  · have indices : source.edges.zipIdx.Pairwise (fun a b => a.2≠b.2) :=
      List.pairwise_map.mp (List.nodup_zipIdx_map_snd source.edges)
    apply indices.imp
    intro a b different vertex firstMember secondMember
    simp only [middle,List.map_map,Function.comp_def] at firstMember secondMember
    obtain ⟨firstPoint,_,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨secondPoint,_,equal⟩ := List.mem_map.mp secondMember
    exact different (Vertex.bend.inj equal).1.symm

theorem subdivisionGraph_wellFormed {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    (wellFormed : source.IsWellFormed) (drawing : PeriodicGridDrawing) (factor : Nat) :
    (subdivisionGraph source drawing factor).IsWellFormed :=
  PeriodicGraph.BendSubdivision.wellFormed wellFormed (middle drawing factor)
    (fun edge _ _ member => middle_only_bends drawing factor edge member)
    (middle_indices_unique source drawing factor)

theorem subdivisionGraph_degreeAtMost {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {bound : Nat} (degree : source.DegreeAtMost bound) (bendDegree : 2≤bound)
    (drawing : PeriodicGridDrawing) (factor : Nat) :
    (subdivisionGraph source drawing factor).DegreeAtMost bound :=
  PeriodicGraph.BendSubdivision.degreeAtMost degree bendDegree (middle drawing factor)
    (fun edge _ _ member => middle_only_bends drawing factor edge member)
    (middle_indices_unique source drawing factor)

theorem subdivisionDrawing_straight {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat)
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged∈(subdivisionGraph source drawing factor).edges.zipIdx) :
    ((subdivisionDrawing source drawing factor).edgeRoute tagged.2).length=2 := by
  have valid : tagged.2<(subdivisionGraph source drawing factor).edges.length := by
    simpa using List.snd_lt_of_mem_zipIdx member
  have lookup := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp member)).2
  simp only [subdivisionDrawing,edgeRoute]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using valid),List.getElem_map,lookup]
  rfl

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
