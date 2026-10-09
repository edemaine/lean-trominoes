/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteNativeVerifier

/-! # One certificate bit per finite edge suffices -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget PeriodicOneInThree

theorem incoming_atom_bound (graph : Input) (vertex : Nat) (literal : PeriodicLiteral Nat)
    (member : literal ∈ incoming graph vertex) : literal.atom<graph.2.length := by
  obtain ⟨incidence,incidenceMember,rfl⟩ := List.mem_map.mp member
  have inEnds := List.mem_of_mem_filter incidenceMember
  rw [ends_eq_incidenceIndices] at inEnds
  obtain ⟨index,indexMember,rfl⟩ := List.mem_map.mp inEnds
  rw [incidenceAt_atom]
  have bound := List.mem_range.mp indexMember
  omega

theorem finiteInwardCount_congr (graph : Input) (first second : Nat → Bool)
    (agree : ∀ edge < graph.2.length, first edge=second edge) (vertex : Nat) :
    finiteInwardCount graph first vertex=finiteInwardCount graph second vertex := by
  unfold finiteInwardCount clauseValues
  congr 1
  apply List.map_congr_left
  intro literal member
  dsimp only
  rw [agree literal.atom (incoming_atom_bound graph vertex literal member)]

theorem finiteOrientation_congr (graph : Input) (wellFormed : IsWellFormed graph)
    (first second : Nat → Bool) (agree : ∀ edge < graph.2.length, first edge=second edge) :
    FiniteIsOrientation graph first ↔ FiniteIsOrientation graph second := by
  rw [finiteIsOrientation_iff_counts _ wellFormed,finiteIsOrientation_iff_counts _ wellFormed]
  unfold FiniteCountConstraints
  simp only [finiteInwardCount_congr graph first second agree]

def certificate (graph : Input) (assignment : Nat → Bool) : List Bool :=
  (List.range graph.2.length).map assignment

theorem certificate_read (graph : Input) (assignment : Nat → Bool) (edge : Nat) (bound : edge<graph.2.length) :
    (certificate graph assignment).getD edge false=assignment edge := by
  unfold certificate
  rw [List.getD_eq_getElem _ _ (by simpa)]
  simp

theorem finiteProblem_iff_certificate (graph : Input) : FiniteProblem graph ↔
    ∃ bits : List Bool, bits.length≤graph.2.length ∧ check (graph,bits)=true := by
  constructor
  · rintro ⟨wellFormed,zero,assignment,oriented⟩
    refine ⟨certificate graph assignment,by simp [certificate],(check_correct _).mpr ⟨wellFormed,zero,?_⟩⟩
    apply (finiteOrientation_congr graph wellFormed assignment
      (fun edge => (certificate graph assignment).getD edge false) (fun edge bound => (certificate_read graph assignment edge bound).symm)).mp
    exact oriented
  · rintro ⟨bits,_,checked⟩
    obtain ⟨wellFormed,zero,oriented⟩ := (check_correct _).mp checked
    exact ⟨wellFormed,zero,_,oriented⟩

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
