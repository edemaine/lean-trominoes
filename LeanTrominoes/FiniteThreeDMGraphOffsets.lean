/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FinitePlanarThreeDMOffsets
import LeanTrominoes.PeriodicThreeDMGraph

/-! # Zero-offset matching has a zero-offset incidence graph -/
namespace LeanTrominoes.PeriodicThreeDM

theorem incidenceGraph_zeroOffsets (problem : PeriodicThreeDM) (zero : problem.ZeroOffsets) :
    ∀ edge∈problem.incidenceGraph.edges,edge.offset=(0,0) := by
  intro edge member
  obtain ⟨tagged,taggedMember,edgeMember⟩ := List.mem_flatMap.mp member
  obtain ⟨color,_,edgeEq⟩ := List.mem_map.mp edgeMember
  subst edge
  exact zero tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember) color
end LeanTrominoes.PeriodicThreeDM
