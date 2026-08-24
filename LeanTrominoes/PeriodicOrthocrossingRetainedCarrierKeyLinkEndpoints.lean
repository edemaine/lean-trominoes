/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-! # Endpoints of per-key retained carrier links -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Both endpoints of a link in one retained carrier-key block are retained
carrier nodes. -/
theorem retainedCompleteCarrierLink_keyBlock_endpoints_mem
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedCompleteCarrierLinks graph key) :
    link.first ∈ retainedDrawingCarrierNodes graph ∧
      link.second ∈ retainedDrawingCarrierNodes graph := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have members :=
    mem_of_mem_consecutivePairs (List.mem_filter.mp pairMem).1
  exact
    ⟨(mem_retainedCompleteCarrierNodes_iff
        graph key pair.1).mp members.1 |>.1,
      (mem_retainedCompleteCarrierNodes_iff
        graph key pair.2).mp members.2 |>.1⟩

end LeanTrominoes.PeriodicOrthocrossing
