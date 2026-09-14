/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBooleanPorts

/-! # Every palette arrangement supplies a legal prefill -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

theorem Atom.prefill_inside_false (a : Atom) {p : Placement Unit} (hp : p ∈ a.motif) :
    p.cells (fun _ => Tromino.L.cells) ⊆ a.pattern.region \ a.booleanOutside (fun _ => false) := by
  rw [boolean_outside_connectors]
  have checked : ∀ p ∈ a.motif, p.cells (fun _ => Tromino.L.cells) ⊆
      a.pattern.region \ connectorOutside a (fun _ => false) := by
    cases a <;> decide +kernel
  exact checked p hp

theorem Atom.prefill_nonoverlap (a : Atom) {p q : Placement Unit} (hp : p ∈ a.motif) (hq : q ∈ a.motif)
    {c : Cell} (hc : c ∈ p.cells (fun _ => Tromino.L.cells)) (hc' : c ∈ q.cells (fun _ => Tromino.L.cells)) :
    p.cells (fun _ => Tromino.L.cells) = q.cells (fun _ => Tromino.L.cells) := by
  have checked : ∀ p ∈ a.motif, ∀ q ∈ a.motif,
      p.cells (fun _ => Tromino.L.cells) = q.cells (fun _ => Tromino.L.cells) ∨
        Disjoint (p.cells (fun _ => Tromino.L.cells)) (q.cells (fun _ => Tromino.L.cells)) := by
    cases a <;> decide +kernel
  rcases checked p hp q hq with eq | disj
  · exact eq
  · exact False.elim (Finset.disjoint_left.mp disj hc hc')

theorem prefill_state_inside {palette : Cell → Fin 24} (o : Occurrence palette)
    {p : Placement Unit} (hp : p ∈ o.entry.1.motif) :
    (p.shift (atomOffset o.location o.entry)).cells (fun _ => Tromino.L.cells) ⊆
      stateTarget o (booleanOutside (fun _ => false) o) := by
  rw [Placement.shift_cells_image]
  unfold stateTarget
  rw [boolean_outside_local]
  exact Finset.image_subset_image (o.entry.1.prefill_inside_false hp)

/-- All preplacements are legal and disjoint, even when the Boolean network
is unsatisfiable. No promise about satisfiability is used here. -/
theorem global_prefill_valid (palette : Cell → Fin 24) :
    Tromino.L.IsPartialTiling Set.univ (globalPrescribed palette) := by
  constructor
  · intro f hf
    obtain ⟨location,p,hp,rfl⟩ := hf
    exact ⟨⟨p.shift (origin location),by rw [Placement.shift_cells_image]⟩,fun _ _ => trivial⟩
  · intro f hf g hg c hc hgc
    rw [← prescribed_union] at hf hg
    obtain ⟨o,p,hp,rfl⟩ := hf
    obtain ⟨o',q,hq,rfl⟩ := hg
    have in₁ := prefill_state_inside o hp hc
    have in₂ := prefill_state_inside o' hq hgc
    rw [boolean_state_target] at in₁ in₂
    obtain ⟨owner,_,unique⟩ := boolean_groups_partition palette (fun _ => false) c
    have eq : o = o' := (unique o in₁).trans (unique o' in₂).symm
    cases eq
    rw [Placement.shift_cells_image] at hc hgc ⊢
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp hgc
    have cellsEq : b = a := Cell.add_left_injective _ eq
    cases cellsEq
    rw [o.entry.1.prefill_nonoverlap hp hq ha hb]
    rw [Placement.shift_cells_image]

end LeanTrominoes.CompletionPattern.LBricks
