/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPortGlobalIndices
import LeanTrominoes.PeriodicOrthocrossingPortRankPrefix

/-! # Port ranks as graph-incidence prefix counts -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The local source-port rank of edge `e` counts matching vertex incidences
strictly before global port `2e`. -/
theorem sourcePortRank_eq_incidencePrefixCount
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    portRank graph (sourcePort tagged.1 tagged.2) =
      (graph.incidences.take (2 * tagged.2)).count tagged.1.source := by
  rw [portRank_eq_sameVertexPrefixLength graph
      (sourcePort tagged.1 tagged.2)
      (sourcePort_mem_allPorts graph taggedMember),
    allPorts_idxOf_sourcePort graph tagged taggedMember]
  rw [
    filter_length_eq_count_map GraphPort.vertex
      (sourcePort tagged.1 tagged.2).vertex,
    List.map_take, allPorts_map_vertex]
  rfl

/-- The local target-port rank of edge `e` counts matching vertex incidences
strictly before global port `2e+1`. -/
theorem targetPortRank_eq_incidencePrefixCount
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (tagged : PeriodicEdge Vertex × Nat)
    (taggedMember : tagged ∈ graph.edges.zipIdx) :
    portRank graph (targetPort tagged.1 tagged.2) =
      (graph.incidences.take (2 * tagged.2 + 1)).count tagged.1.target := by
  rw [portRank_eq_sameVertexPrefixLength graph
      (targetPort tagged.1 tagged.2)
      (targetPort_mem_allPorts graph taggedMember),
    allPorts_idxOf_targetPort graph tagged taggedMember]
  rw [
    filter_length_eq_count_map GraphPort.vertex
      (targetPort tagged.1 tagged.2).vertex,
    List.map_take, allPorts_map_vertex]
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
