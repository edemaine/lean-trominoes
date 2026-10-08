/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMContractionEndpointContacts
import LeanTrominoes.PeriodicThreeDMLineDecision

/-! # When degree-two contraction preserves Manhattan locality -/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

def IncidenceOffsetsComparable (problem : PeriodicThreeDM) : Prop :=
  ∀ color atom, ∀ first ∈ problem.incidences color atom, ∀ second ∈ problem.incidences color atom,
    first.offset = (0,0) ∨ second.offset = (0,0) ∨ first.offset = second.offset

theorem contractedGraph_isLocal {problem : PeriodicThreeDM} (locality : problem.IsLocal)
    (comparable : problem.IncidenceOffsetsComparable) : problem.contractedGraph.IsLocal := by
  intro edge member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  have incidences := contractedEdge_incidence_members_of_mem problem originalMember
  have sourceBound := incidence_offset_local locality original.color original.atom incidences.1
  have targetBound := incidence_offset_local locality original.color original.atom incidences.2.1
  have offsets := comparable original.color original.atom _ incidences.1 _ incidences.2.1
  cases original with
  | retained color atom incidence => exact sourceBound
  | through color atom first second =>
    change first.offset.1.natAbs + first.offset.2.natAbs ≤ 1 at sourceBound
    change second.offset.1.natAbs + second.offset.2.natAbs ≤ 1 at targetBound
    change first.offset = (0,0) ∨ second.offset = (0,0) ∨ first.offset = second.offset at offsets
    rcases offsets with firstZero | secondZero | same
    · simpa [ContractedEdge.toPeriodicEdge,PeriodicEdge.span,Cell.sub,firstZero] using targetBound
    · simpa [ContractedEdge.toPeriodicEdge,PeriodicEdge.span,Cell.sub,secondZero] using sourceBound
    · simp [ContractedEdge.toPeriodicEdge,PeriodicEdge.span,Cell.sub,same]

end LeanTrominoes.PeriodicThreeDM
