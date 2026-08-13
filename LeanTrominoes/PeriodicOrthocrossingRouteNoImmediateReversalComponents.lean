/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOrthogonal
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-!
# No-reversal certificates for orthocrossing route components

Constructed orthocrossing routes have three pieces: a source fanout, an
edge-specific core, and a translated reversed target fanout.  This file
certifies that each piece has no immediate reversal and records the endpoint
directions needed to splice the pieces.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A source fanout never immediately reverses. -/
theorem fanout_hasNoImmediateReversal (centerX portColumn : Int) :
    AxisDirection.HasNoImmediateReversal
      (fanout centerX portColumn) := by
  by_cases same : centerX = portColumn
  · simp [fanout, same, AxisDirection.HasNoImmediateReversal]
  · simp [fanout, same, AxisDirection.HasNoImmediateReversal,
      AxisDirection.between, AxisDirection.opposite]
    split_ifs <;> simp_all

/-- Every source fanout reaches its port while heading north. -/
theorem fanout_lastDirection (centerX portColumn : Int) :
    AxisDirection.polylineLastDirection
        (fanout centerX portColumn) =
      .north := by
  by_cases same : centerX = portColumn
  · subst portColumn
    simp [fanout, AxisDirection.polylineLastDirection,
      AxisDirection.polylineFirstDirection,
      AxisDirection.between, AxisDirection.opposite]
  · simp [fanout, same, AxisDirection.polylineLastDirection,
      AxisDirection.polylineFirstDirection,
      AxisDirection.between, AxisDirection.opposite]

/-- Reversing and translating a fanout preserves its no-reversal
certificate. -/
theorem translated_reverse_fanout_hasNoImmediateReversal
    (centerX portColumn : Int) (translate : Cell) :
    AxisDirection.HasNoImmediateReversal
      (translatePolyline translate
        (fanout centerX portColumn).reverse) := by
  have reversed :=
    (fanout_hasNoImmediateReversal centerX portColumn).reverse
      (fanout_orthogonal centerX portColumn)
  exact reversed.translate translate

/-- A reversed target fanout leaves its port while heading south. -/
theorem translated_reverse_fanout_firstDirection
    (centerX portColumn : Int) (translate : Cell) :
    AxisDirection.polylineFirstDirection
        (translatePolyline translate
          (fanout centerX portColumn).reverse) =
      .south := by
  by_cases same : centerX = portColumn
  · subst portColumn
    simp [translatePolyline, fanout,
      AxisDirection.polylineFirstDirection,
      AxisDirection.between, Cell.add]
  · rcases translate with ⟨translateX, translateY⟩
    simp [translatePolyline, fanout, same,
      AxisDirection.polylineFirstDirection,
      AxisDirection.between, Cell.add]

/-- Translated reversed fanouts remain nondegenerate. -/
theorem translated_reverse_fanout_length_ge_two
    (centerX portColumn : Int) (translate : Cell) :
    2 ≤
      (translatePolyline translate
        (fanout centerX portColumn).reverse).length := by
  simp [translatePolyline]
  exact fanout_length_ge_two centerX portColumn

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 800000 in
/-- Every local private-track edge core avoids immediate reversals. -/
theorem edgeCore_hasNoImmediateReversal
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    AxisDirection.HasNoImmediateReversal
      (edgeCore graph taggedEdge.1 taggedEdge.2) := by
  let source := sourcePort taggedEdge.1 taggedEdge.2
  let target := targetPort taggedEdge.1 taggedEdge.2
  have sourceMem : source ∈ allPorts graph :=
    sourcePort_mem_allPorts graph edgeMem
  have targetMem : target ∈ allPorts graph :=
    targetPort_mem_allPorts graph edgeMem
  have sourceBounds := portX_bounds wellFormed degree sourceMem
  have targetBounds := portX_bounds wellFormed degree targetMem
  have sourceBeforeGate :=
    portX_lt_edgeGateX wellFormed degree sourceMem taggedEdge.2
  have targetBeforeGate :=
    portX_lt_edgeGateX wellFormed degree targetMem taggedEdge.2
  have tracks := edgeTrack_bounds graph edgeMem
  have gateBounds := edgeGateX_bounds graph edgeMem
  have portsDifferent :=
    sourcePortX_ne_targetPortX wellFormed degree edgeMem
  have sizePositive := drawingGridSize_pos graph
  dsimp [source, target] at sourceMem targetMem sourceBounds targetBounds sourceBeforeGate targetBeforeGate
  rcases offset_eq_of_span_le_one taggedEdge.1 edgeLocal with
      offset | offset | offset | offset | offset
  all_goals
    simp [edgeCore, offset,
      AxisDirection.HasNoImmediateReversal,
      AxisDirection.between, AxisDirection.opposite,
      Cell.add, Cell.scale]
  all_goals split_ifs <;> try omega
  all_goals
    simp [AxisDirection.HasNoImmediateReversal,
      AxisDirection.between, AxisDirection.opposite]
  all_goals split_ifs <;> try omega <;> simp
  all_goals simp

/-- Every local edge core starts by heading north from its source port. -/
theorem edgeCore_firstDirection
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    AxisDirection.polylineFirstDirection
        (edgeCore graph taggedEdge.1 taggedEdge.2) =
      .north := by
  have tracks := edgeTrack_bounds graph edgeMem
  rcases offset_eq_of_span_le_one taggedEdge.1 edgeLocal with
      offset | offset | offset | offset | offset
  all_goals unfold edgeCore
  all_goals simp only [offset]
  all_goals first | split | skip
  all_goals
    simp [AxisDirection.polylineFirstDirection,
      AxisDirection.between]
  all_goals split_ifs <;> simp_all <;> omega

/-- Every local edge core finishes by heading south into its target port. -/
theorem edgeCore_lastDirection
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    AxisDirection.polylineLastDirection
        (edgeCore graph taggedEdge.1 taggedEdge.2) =
      .south := by
  have tracks := edgeTrack_bounds graph edgeMem
  rcases offset_eq_of_span_le_one taggedEdge.1 edgeLocal with
      offset | offset | offset | offset | offset
  all_goals unfold edgeCore
  all_goals simp only [offset]
  all_goals first | split | skip
  all_goals
    simp [AxisDirection.polylineLastDirection,
      AxisDirection.polylineFirstDirection,
      AxisDirection.between, AxisDirection.opposite,
      Cell.add, Cell.scale]
  all_goals split_ifs <;> try simp_all <;> try omega
  all_goals omega

end PeriodicOrthocrossing
end LeanTrominoes
