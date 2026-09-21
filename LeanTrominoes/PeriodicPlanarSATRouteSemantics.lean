/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATRouteClauseLoop
import LeanTrominoes.PeriodicPlanarSATRouteMachine

/-! # Correctness of the compiled incidence-route verifier -/
namespace LeanTrominoes.PeriodicPlanarSAT.RouteProgram
open PeriodicCNF.IncidenceFields

theorem program_truth (input : Input Nat) (valid : IncidenceCounts.Valid input) :
    program.value (RouteInput.context input) ≠ 0 ↔ input.2.RoutesMatch input.1.incidenceGraph := by
  rw [program_truth_headers input valid,← addressRoutesMatch_iff]
  constructor
  · intro checked entry member
    obtain ⟨h,c,hc,k,hk,rfl⟩ := (edgeEntries_mem_iff input.1 entry).mp member
    exact checked h c hc k hk
  · intro checked h c hc k hk
    exact checked _ ((edgeEntries_mem_iff input.1 _).mpr ⟨h,c,hc,k,hk,rfl⟩)

theorem result_correct (input : Input Nat) (valid : IncidenceCounts.Valid input) :
    result input=true ↔ input.2.RoutesMatch input.1.incidenceGraph := by
  simp only [result,decide_eq_true_eq,program_truth input valid]

end LeanTrominoes.PeriodicPlanarSAT.RouteProgram
