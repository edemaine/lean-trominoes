/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEndpointContacts
import LeanTrominoes.Graphs.Core.PeriodicGraphOrbitCertificate

/-! # Endpoint contacts can be checked by vertex residues

Two listed route points have intersecting translation orbits exactly when
their coordinates agree modulo the positive drawing period. This finite
criterion needs no bound on the chosen representatives.
-/
namespace LeanTrominoes.PeriodicGridDrawing

/-- Distinct listed point occurrences in the same periodic orbit must both
be outer endpoints of their routes. -/
def EndpointResidues (drawing : PeriodicGridDrawing) : Prop :=
  ∀ a ∈ drawing.indexedRoutePoints, ∀ b ∈ drawing.indexedRoutePoints,
    a ≠ b → OrbitCertificate.residue drawing.gridSize a.point =
      OrbitCertificate.residue drawing.gridSize b.point → a.IsEndpoint ∧ b.IsEndpoint

theorem endpointResidues_iff (drawing : PeriodicGridDrawing) :
    drawing.EndpointResidues ↔ drawing.RoutePointsMeetOnlyAtEndpoints := by
  constructor
  · intro finite a ha b hb t u different collision
    by_cases unequal : a ≠ b
    · apply finite a ha b hb unequal
      have equal := congrArg (OrbitCertificate.residue drawing.gridSize) collision
      simpa [OrbitCertificate.residue,periodTranslation,Cell.add,Cell.scale,Int.add_emod] using equal
    · have same : a=b := not_ne_iff.mp unequal
      subst b
      have shifts : Cell.scale (drawing.gridSize : ℤ) t=Cell.scale (drawing.gridSize : ℤ) u := by
        apply Prod.ext
        · have h := congrArg Prod.fst collision
          simp only [Cell.add,periodTranslation,Cell.scale] at h ⊢
          omega
        · have h := congrArg Prod.snd collision
          simp only [Cell.add,periodTranslation,Cell.scale] at h ⊢
          omega
      have sameShift : t=u := Cell.scale_injective (by exact_mod_cast Nat.ne_of_gt (show 0 < drawing.gridSize by unfold gridSize; omega)) shifts
      subst u
      exact False.elim (different rfl)
  · intro global a ha b hb unequal sameResidue
    obtain ⟨t,collision⟩ := (OrbitCertificate.residue_eq_iff drawing.gridSize a.point b.point).mp sameResidue
    have different : RoutePointOccurrenceKey a (0,0) ≠ RoutePointOccurrenceKey b t := by
      intro same
      have route := congrArg (fun key : ℕ×ℕ×Cell => key.1) same
      have point := congrArg (fun key : ℕ×ℕ×Cell => key.2.1) same
      exact unequal (indexedRoutePoint_eq_of_mem_of_indices_eq ha hb route point)
    apply global a ha b hb (0,0) t different
    simpa only [periodTranslation,Cell.scale,Cell.add,Int.mul_zero,Int.add_zero,Int.add_comm] using collision

end LeanTrominoes.PeriodicGridDrawing
