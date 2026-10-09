/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGraph
import Mathlib.Data.List.Count

/-! # Subdividing periodic edges into chains preserves the degree bound -/
namespace LeanTrominoes.PeriodicGraph.BendSubdivision

inductive Vertex (Original : Type*) where
  | original (vertex : Original)
  | bend (edgeIndex pointIndex : Nat)
  deriving DecidableEq, Repr

def chainEdges {V : Type*} : List (V × Cell) → List (PeriodicEdge V)
  | first :: second :: rest =>
      ⟨first.1,second.1,Cell.sub second.2 first.2⟩ :: chainEdges (second :: rest)
  | _ => []

theorem chainEdges_endpoints_mem {V : Type*} {points : List (V × Cell)} {edge : PeriodicEdge V}
    (member : edge∈chainEdges points) : edge.source∈points.map Prod.fst ∧ edge.target∈points.map Prod.fst := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [chainEdges] at member
  | cons_cons first second rest _ induction =>
      simp only [chainEdges,List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have endpoints := induction second member
        exact ⟨List.mem_cons_of_mem first.1 endpoints.1,List.mem_cons_of_mem first.1 endpoints.2⟩

theorem chainEdges_count {V : Type*} [DecidableEq V] (first last : V × Cell)
    (middle : List (V × Cell)) (wanted : V) :
    ((chainEdges (first::middle++[last])).flatMap PeriodicEdge.incidences).count wanted =
      [first.1,last.1].count wanted+2*(middle.map Prod.fst).count wanted := by
  induction middle generalizing first with
  | nil => simp [chainEdges,PeriodicEdge.incidences]
  | cons next rest induction =>
      change ([first.1,next.1]++
        (chainEdges (next::rest++[last])).flatMap PeriodicEdge.incidences).count wanted =
          [first.1,last.1].count wanted+2*(next.1::rest.map Prod.fst).count wanted
      rw [List.count_append,induction next]
      simp only [List.count_cons,List.count_nil]
      split <;> split <;> split <;> omega

def nodes {V : Type*} (tagged : PeriodicEdge V × Nat) (middle : List (Vertex V × Cell)) :
    List (Vertex V × Cell) :=
  (.original tagged.1.source,(0,0))::middle++[(.original tagged.1.target,tagged.1.offset)]

def graph {V : Type*} (source : PeriodicGraph V)
    (middle : PeriodicEdge V × Nat → List (Vertex V × Cell)) : PeriodicGraph (Vertex V) where
  vertices := source.vertices.map Vertex.original ++
    source.edges.zipIdx.flatMap (fun tagged => (middle tagged).map Prod.fst)
  edges := source.edges.zipIdx.flatMap (fun tagged => chainEdges (nodes tagged (middle tagged)))

theorem wellFormed {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    (wellFormed : source.IsWellFormed)
    (middle : PeriodicEdge V × Nat → List (Vertex V × Cell))
    (onlyBends : ∀ edge∈source.edges.zipIdx, ∀ entry∈middle edge, ∃ i j, entry.1=Vertex.bend i j)
    (unique : (source.edges.zipIdx.flatMap fun edge => (middle edge).map Prod.fst).Nodup) :
    (graph source middle).IsWellFormed := by
  constructor
  · rw [graph,List.nodup_append]
    refine ⟨wellFormed.1.map (fun _ _ equal => Vertex.original.inj equal),unique,?_⟩
    intro first firstMember second secondMember equal
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨edge,edgeMember,member⟩ := List.mem_flatMap.mp secondMember
    obtain ⟨entry,entryMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨i,j,bend⟩ := onlyBends edge edgeMember entry entryMember
    rw [bend] at equal
    cases equal
  · intro edge edgeMember
    obtain ⟨tagged,taggedMember,member⟩ := List.mem_flatMap.mp edgeMember
    have endpoints := chainEdges_endpoints_mem member
    have nodesListed (vertex : Vertex V) (member : vertex∈(nodes tagged (middle tagged)).map Prod.fst) :
        vertex∈(graph source middle).vertices := by
      simp only [nodes,List.map_cons,List.map_append,List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
      rcases member with (rfl | member) | rfl
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,(wellFormed.2 tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)).1,rfl⟩
      · apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨tagged,taggedMember,member⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨_,(wellFormed.2 tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)).2,rfl⟩
    exact ⟨nodesListed edge.source endpoints.1,nodesListed edge.target endpoints.2⟩

theorem incidence_count {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (middle : PeriodicEdge V × Nat → List (Vertex V × Cell)) (wanted : Vertex V) :
    (graph source middle).incidences.count wanted =
      (source.incidences.map Vertex.original).count wanted+
        2*(source.edges.zipIdx.flatMap (fun tagged => (middle tagged).map Prod.fst)).count wanted := by
  have tagged (edges : List (PeriodicEdge V × Nat)) :
      ((edges.flatMap fun edge => chainEdges (nodes edge (middle edge))).flatMap PeriodicEdge.incidences).count wanted =
        (edges.flatMap fun edge => [Vertex.original edge.1.source,Vertex.original edge.1.target]).count wanted+
          2*(edges.flatMap fun edge => (middle edge).map Prod.fst).count wanted := by
    induction edges with
    | nil => simp
    | cons edge rest induction =>
        simp only [List.flatMap_cons,List.flatMap_append,List.count_append]
        rw [show nodes edge (middle edge)=
          (.original edge.1.source,(0,0))::middle edge++[(.original edge.1.target,edge.1.offset)] from rfl,
          chainEdges_count,induction]
        dsimp only [Prod.fst]
        omega
  rw [show (graph source middle).incidences=
    (source.edges.zipIdx.flatMap fun edge => chainEdges (nodes edge (middle edge))).flatMap PeriodicEdge.incidences from rfl,
    tagged]
  have endpoints : (source.edges.zipIdx.flatMap fun edge =>
      [Vertex.original edge.1.source,Vertex.original edge.1.target])=source.incidences.map Vertex.original := by
    rw [PeriodicCNF.zipIdx_flatMap_fst
      (fun edge : PeriodicEdge V => [Vertex.original edge.source,Vertex.original edge.target]) source.edges 0,
      PeriodicGraph.incidences,List.map_flatMap]
    rfl
  rw [endpoints]

theorem degreeAtMost {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {bound : Nat}
    (degree : source.DegreeAtMost bound) (bendDegree : 2≤bound)
    (middle : PeriodicEdge V × Nat → List (Vertex V × Cell))
    (onlyBends : ∀ edge∈source.edges.zipIdx, ∀ entry∈middle edge, ∃ i j, entry.1=Vertex.bend i j)
    (unique : (source.edges.zipIdx.flatMap fun edge => (middle edge).map Prod.fst).Nodup) :
    (graph source middle).DegreeAtMost bound := by
  let bends := source.edges.zipIdx.flatMap fun edge => (middle edge).map Prod.fst
  have absent (vertex : V) : Vertex.original vertex∉bends := by
    intro member
    obtain ⟨edge,edgeMember,member⟩ := List.mem_flatMap.mp member
    obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp member
    obtain ⟨i,j,bend⟩ := onlyBends edge edgeMember entry entryMember
    rw [bend] at equal
    cases equal
  intro vertex
  rw [incidence_count]
  cases vertex with
  | original vertex =>
      have zero : bends.count (.original vertex)=0 := List.count_eq_zero.mpr (absent vertex)
      change (source.incidences.map Vertex.original).count (.original vertex)+2*bends.count (.original vertex)≤bound
      rw [zero]
      have count : (source.incidences.map Vertex.original).count (.original vertex)=source.incidences.count vertex := by
        exact List.count_map_of_injective _ _ (fun a b equal => Vertex.original.inj equal) _
      simpa [count] using degree vertex
  | bend i j =>
      have zero : (source.incidences.map Vertex.original).count (.bend i j)=0 := by
        apply List.count_eq_zero.mpr
        simp
      rw [zero,zero_add]
      have atMost : bends.count (.bend i j)≤1 := List.nodup_iff_count_le_one.mp unique _
      change 2*bends.count (.bend i j)≤bound
      omega

end LeanTrominoes.PeriodicGraph.BendSubdivision
