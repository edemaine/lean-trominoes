/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParentPorts
import LeanTrominoes.PeriodicGridDrawingRectangleInputNoninterlacing

/-! # A finite, bounded-depth rectangle matching assembled from original edge ports -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

theorem Port.inside_of_margin_le {port : Port} {width height small large : Int}
    (inside : port.Inside width height large) (marginLe : small ≤ large) : port.Inside width height small := by
  unfold Inside at inside ⊢
  exact ⟨marginLe.trans_lt inside.1,inside.2.trans_le (sub_le_sub_left marginLe _)⟩

end LeanTrominoes.OrthogonalBoundaryRouting
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

def rectangleParentChord {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) : Option (RectanglePortKey Vertex × RectanglePortKey Vertex) :=
  match rectangleParentPorts graph drawing column parent with
  | [first,last] => some (first,last)
  | _ => none

theorem rectangleParentChord_some_iff {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) :
    rectangleParentChord graph drawing column parent = some (first,last) ↔ rectangleParentPorts graph drawing column parent = [first,last] := by
  unfold rectangleParentChord
  generalize rectangleParentPorts graph drawing column parent = ports
  cases ports with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b rest =>
      cases rest with
      | nil => simp
      | cons c rest => simp

theorem rectangleParentChord_data {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    first.Valid graph drawing column ∧ last.Valid graph drawing column ∧ first.parentKey = parent ∧ last.parentKey = parent ∧
      (first.virtualPort graph drawing column).Before (last.virtualPort graph drawing column) := by
  have ports := (rectangleParentChord_some_iff graph drawing column parent first last).mp lookup
  have firstAt : first ∈ rectangleParentPorts graph drawing column parent := by rw [ports]; simp
  have lastAt : last ∈ rectangleParentPorts graph drawing column parent := by rw [ports]; simp
  have firstData := rectangleParentPorts_valid graph drawing column parent firstAt
  have lastData := rectangleParentPorts_valid graph drawing column parent lastAt
  have ordered := rectangleParentPorts_ordered graph drawing column parent
  rw [ports] at ordered
  exact ⟨firstData.1,lastData.1,firstData.2,lastData.2,by simpa using ordered⟩

def rectangleChordKeys {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : List (RectanglePortKey Vertex × RectanglePortKey Vertex) :=
  (nineEdgeCopies graph).filterMap (rectangleParentChord graph drawing column)

def rectangleChordFamily {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : Finset Chord :=
  ((rectangleChordKeys graph drawing column).map fun keys =>
    (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)).toFinset

theorem rectangleChordFamily_sources {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) :
    ∃ parent ∈ nineEdgeCopies graph, ∃ first last : RectanglePortKey Vertex,
      rectangleParentChord graph drawing column parent = some (first,last) ∧
        chord = (first.integralPort graph drawing column,last.integralPort graph drawing column) := by
  obtain ⟨keys,keysAt,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  obtain ⟨parent,parentAt,lookup⟩ := List.mem_filterMap.mp keysAt
  exact ⟨parent,parentAt,keys.1,keys.2,by simpa only [Prod.eta] using lookup,equal.symm⟩

theorem rectangleChordFamily_card_bound {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) (column : Nat) :
    (rectangleChordFamily graph drawing column).card ≤ crossingBound drawing.gridSize := by
  have finite := List.toFinset_card_le ((rectangleChordKeys graph drawing column).map fun keys =>
    (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column))
  have filtered := List.length_filterMap_le (rectangleParentChord graph drawing column) (nineEdgeCopies graph)
  have copies := nineEdgeCopies_length graph
  have bound := nine_copy_edge_count_bound compatible degree
  simp only [List.length_map] at finite
  unfold rectangleChordFamily rectangleChordKeys crossingBound at *
  omega

theorem rectangleChordFamily_room {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) (column : Nat) :
    2*((rectangleChordFamily graph drawing column).card : Int) < drawing.paddedSlabWidth ∧
      2*((rectangleChordFamily graph drawing column).card : Int) < paddedGridSize drawing.gridSize := by
  have bound : ((rectangleChordFamily graph drawing column).card : Int) ≤ crossingBound drawing.gridSize := by
    exact_mod_cast rectangleChordFamily_card_bound compatible degree column
  have room := paddedSlab_room drawing
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  constructor <;> nlinarith [room.1,room.2]

theorem rectangleChordFamily_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) :
    chord.1.Inside drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (rectangleChordFamily graph drawing column).card ∧
      chord.2.Inside drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) (rectangleChordFamily graph drawing column).card ∧ chord.1.Before chord.2 := by
  obtain ⟨parent,_,first,last,lookup,rfl⟩ := rectangleChordFamily_sources member
  have data := rectangleParentChord_data graph drawing column parent lookup
  have bound : ((rectangleChordFamily graph drawing column).card : Int) ≤ 2*crossingBound drawing.gridSize := by
    have smaller : ((rectangleChordFamily graph drawing column).card : Int) ≤ crossingBound drawing.gridSize := by
      exact_mod_cast rectangleChordFamily_card_bound planar.1.1 degree column
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  exact ⟨Port.inside_of_margin_le (rectanglePort_integral_inside planar degree graphLocal straight column data.1) bound,
    Port.inside_of_margin_le (rectanglePort_integral_inside planar degree graphLocal straight column data.2.1) bound,
    rectanglePort_preserves_before planar degree graphLocal straight column (first := first) (second := last) data.1 data.2.1 data.2.2.2.2⟩

theorem rectangleChordFamily_noninterlacing {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {first last : Chord} (firstMember : first ∈ rectangleChordFamily graph drawing column)
    (lastMember : last ∈ rectangleChordFamily graph drawing column) (different : first ≠ last) : Noninterlacing first last := by
  obtain ⟨firstParent,_,a,b,firstLookup,firstEq⟩ := rectangleChordFamily_sources firstMember
  obtain ⟨lastParent,_,c,d,lastLookup,lastEq⟩ := rectangleChordFamily_sources lastMember
  have firstData := rectangleParentChord_data graph drawing column firstParent firstLookup
  have lastData := rectangleParentChord_data graph drawing column lastParent lastLookup
  have parentsDifferent : firstParent ≠ lastParent := by
    intro same
    rw [same] at firstLookup
    have keysEqual := Option.some.inj (firstLookup.symm.trans lastLookup)
    have firstKey := congrArg Prod.fst keysEqual
    have lastKey := congrArg Prod.snd keysEqual
    dsimp only at firstKey lastKey
    apply different
    rw [firstEq,lastEq,firstKey,lastKey]
  rw [firstEq,lastEq]
  exact rectangle_integral_input_noninterlacing planar degree graphLocal straight column (a := a) (b := b) (c := c) (d := d)
    firstData.1 firstData.2.1 lastData.1 lastData.2.1
    (firstData.2.2.1.trans firstData.2.2.2.1.symm) (lastData.2.2.1.trans lastData.2.2.2.1.symm)
    (by rwa [firstData.2.2.1,lastData.2.2.1]) firstData.2.2.2.2 lastData.2.2.2.2

end LeanTrominoes.PeriodicGridDrawing
