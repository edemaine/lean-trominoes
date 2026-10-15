/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Core.PeriodicGraphCoreData
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Sigma

/-! # Finite presentations of periodic graphs -/
namespace LeanTrominoes

namespace PeriodicEdge

/-- Product representation used by the standard computability encoding. -/
def equivData {Vertex : Type*} :
    PeriodicEdge Vertex ≃ Vertex × Vertex × Cell where
  toFun edge := (edge.source, edge.target, edge.offset)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv edge := by cases edge; rfl
  right_inv data := by rcases data with ⟨source, target, offset⟩; rfl

noncomputable instance {Vertex : Type*} [Primcodable Vertex] :
    Primcodable (PeriodicEdge Vertex) :=
  Primcodable.ofEquiv (Vertex × Vertex × Cell) equivData

/-- Manhattan length of the translation between the two endpoint cells. -/
def span {Vertex : Type*} (edge : PeriodicEdge Vertex) : Nat :=
  edge.offset.1.natAbs + edge.offset.2.natAbs

/-- The two endpoint protovertices, with a loop deliberately counted twice. -/
def incidences {Vertex : Type*} (edge : PeriodicEdge Vertex) : List Vertex :=
  [edge.source, edge.target]

/-- Whether two lifted vertices are the endpoints of one translate of this
protoedge.  The disjunction makes the undirected symmetry explicit. -/
def Connects {Vertex : Type*} (edge : PeriodicEdge Vertex)
    (first second : Vertex × Cell) : Prop :=
  (∃ translate,
      first = (edge.source, translate) ∧
      second = (edge.target, Cell.add translate edge.offset)) ∨
    ∃ translate,
      second = (edge.source, translate) ∧
      first = (edge.target, Cell.add translate edge.offset)

theorem connects_symm {Vertex : Type*}
    {edge : PeriodicEdge Vertex} {first second : Vertex × Cell}
    (connects : edge.Connects first second) :
    edge.Connects second first :=
  connects.elim Or.inr Or.inl

end PeriodicEdge

/-- A finite presentation of an infinite graph invariant under every
translation in `ℤ²`. -/
structure PeriodicGraph (Vertex : Type*) where
  vertices : List Vertex
  edges : List (PeriodicEdge Vertex)
  deriving DecidableEq, Repr

namespace PeriodicGraph

/-- Pair-of-lists representation used by the computability encoding. -/
def equivData {Vertex : Type*} :
    PeriodicGraph Vertex ≃ List Vertex × List (PeriodicEdge Vertex) where
  toFun graph := (graph.vertices, graph.edges)
  invFun data := ⟨data.1, data.2⟩
  left_inv graph := by cases graph; rfl
  right_inv _ := rfl

noncomputable instance {Vertex : Type*} [Primcodable Vertex] :
    Primcodable (PeriodicGraph Vertex) :=
  Primcodable.ofEquiv (List Vertex × List (PeriodicEdge Vertex)) equivData

/-- Every listed edge names listed endpoints, and the protovertex list has no
duplicates. -/
def IsWellFormed {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : Prop :=
  graph.vertices.Nodup ∧
    ∀ edge ∈ graph.edges,
      edge.source ∈ graph.vertices ∧ edge.target ∈ graph.vertices

/-- The paper's locality condition for a graph presentation. -/
def IsLocal {Vertex : Type*} (graph : PeriodicGraph Vertex) : Prop :=
  ∀ edge ∈ graph.edges, edge.span ≤ 1

/-- All edge-end occurrences in the finite presentation. -/
def incidences {Vertex : Type*} (graph : PeriodicGraph Vertex) : List Vertex :=
  graph.edges.flatMap PeriodicEdge.incidences

/-- Every protovertex has at most `bound` incident edge ends.  A loop
contributes two, matching graph-theoretic degree. -/
def DegreeAtMost {Vertex : Type*} [BEq Vertex] [LawfulBEq Vertex]
    (bound : Nat) (graph : PeriodicGraph Vertex) : Prop :=
  ∀ vertex, graph.incidences.count vertex ≤ bound

/-- Adjacency in the infinite periodic lift. -/
def Adjacent {Vertex : Type*} (graph : PeriodicGraph Vertex)
    (first second : Vertex × Cell) : Prop :=
  ∃ edge ∈ graph.edges, edge.Connects first second

theorem adjacent_symm {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {first second : Vertex × Cell}
    (adjacent : graph.Adjacent first second) :
    graph.Adjacent second first := by
  rcases adjacent with ⟨edge, edge_mem, connects⟩
  exact ⟨edge, edge_mem, PeriodicEdge.connects_symm connects⟩

end PeriodicGraph

end LeanTrominoes
