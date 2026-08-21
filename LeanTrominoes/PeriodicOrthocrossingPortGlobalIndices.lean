/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicOrthocrossingPorts

/-! # Exact global indices of constructed graph ports -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- An entry of a zero-based indexed list occurs at its own advertised index
when the indexed list is indexed a second time. -/
theorem zipIdx_self_mem_zipIdx
    {Value : Type*} (values : List Value) (tagged : Value × Nat)
    (taggedMember : tagged ∈ values.zipIdx) :
    (tagged, tagged.2) ∈ values.zipIdx.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zipIdx,
    (List.mem_zipIdx_iff_getElem?).mp taggedMember]
  simp

/-- Indexing the flattened two-port blocks assigns consecutive indices
`2e` and `2e+1` to edge `e`. -/
theorem allPorts_zipIdx_eq_edgeBlocks
    {Vertex : Type} (graph : PeriodicGraph Vertex) :
    (allPorts graph).zipIdx =
      graph.edges.zipIdx.zipIdx.flatMap fun tagged =>
        (edgePorts tagged.1).zipIdx (2 * tagged.2) := by
  unfold allPorts
  simpa using
    (IndexedListScan.flatMap_zipIdx_eq_zipIdx_flatMap_fixed_zero
      graph.edges.zipIdx edgePorts 2 0 (fun _ => rfl))

/-- The source port of edge index `e` is global port `2e`. -/
theorem sourcePort_mem_allPorts_zipIdx
    {Vertex : Type} (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    (sourcePort tagged.1 tagged.2, 2 * tagged.2) ∈
      (allPorts graph).zipIdx := by
  rw [allPorts_zipIdx_eq_edgeBlocks]
  apply List.mem_flatMap.mpr
  refine ⟨(tagged, tagged.2),
    zipIdx_self_mem_zipIdx graph.edges tagged taggedMember, ?_⟩
  simp [edgePorts, sourcePort]

/-- The target port of edge index `e` is global port `2e+1`. -/
theorem targetPort_mem_allPorts_zipIdx
    {Vertex : Type} (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    (targetPort tagged.1 tagged.2, 2 * tagged.2 + 1) ∈
      (allPorts graph).zipIdx := by
  rw [allPorts_zipIdx_eq_edgeBlocks]
  apply List.mem_flatMap.mpr
  refine ⟨(tagged, tagged.2),
    zipIdx_self_mem_zipIdx graph.edges tagged taggedMember, ?_⟩
  simp [edgePorts, targetPort]

/-- Closed first-occurrence index of a listed source port. -/
theorem allPorts_idxOf_sourcePort
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    (allPorts graph).idxOf (sourcePort tagged.1 tagged.2) =
      2 * tagged.2 := by
  exact IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
    (allPorts graph) (allPorts_nodup graph)
    (sourcePort tagged.1 tagged.2, 2 * tagged.2)
    (sourcePort_mem_allPorts_zipIdx graph tagged taggedMember)

/-- Closed first-occurrence index of a listed target port. -/
theorem allPorts_idxOf_targetPort
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    (allPorts graph).idxOf (targetPort tagged.1 tagged.2) =
      2 * tagged.2 + 1 := by
  exact IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
    (allPorts graph) (allPorts_nodup graph)
    (targetPort tagged.1 tagged.2, 2 * tagged.2 + 1)
    (targetPort_mem_allPorts_zipIdx graph tagged taggedMember)

end PeriodicOrthocrossing
end LeanTrominoes
