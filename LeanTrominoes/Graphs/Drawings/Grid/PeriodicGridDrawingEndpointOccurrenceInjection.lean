/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationEndpointRays

/-! # An indexed graph port identifies its original edge and endpoint kind -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing GeneralVertexNormalization

theorem endpointPort_occurrence_injective {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    {firstTarget lastTarget : Bool} (portsEq : endpointPort first firstTarget = endpointPort last lastTarget) :
    first = last ∧ firstTarget = lastTarget := by
  have indexEq : first.2 = last.2 := by
    have index := congrArg GraphPort.edgeIndex portsEq
    cases firstTarget <;> cases lastTarget <;> simpa [endpointPort,sourcePort,targetPort] using index
  have firstLookup := List.mem_zipIdx_iff_getElem?.mp firstMember
  have lastLookup := List.mem_zipIdx_iff_getElem?.mp lastMember
  rw [← indexEq] at lastLookup
  have edgeEq := Option.some.inj (firstLookup.symm.trans lastLookup)
  refine ⟨Prod.ext edgeEq indexEq,?_⟩
  cases firstTarget <;> cases lastTarget <;> simp_all [endpointPort,sourcePort,targetPort]

end LeanTrominoes.PeriodicGridDrawing
