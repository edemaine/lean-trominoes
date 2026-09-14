/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIAtomBarriers

/-! # The fixed cells of I-subbricks are actual prescribed tiles -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- A cell is prefilled by one of the subbricks of this palette entry. -/
def FilledAt (i : Fin 24) (c : Cell) : Prop :=
  ∃ entry ∈ layout i, Cell.sub c entry.2 ∈ entry.1.fixed

instance (i : Fin 24) (c : Cell) : Decidable (FilledAt i c) := by
  unfold FilledAt
  infer_instance

theorem Atom.prefill_mem (a : Atom) (p : Placement Unit) :
    p ∈ a.pattern.prefill ↔ p ∈ a.motif := by cases a <;> rfl

theorem Atom.kind_eq (a : Atom) : a.pattern.tromino = .I := by cases a <;> rfl

theorem Atom.fixed_mem (a : Atom) (c : Cell) :
    c ∈ a.fixed ↔ ∃ p ∈ a.motif, c ∈ p.cells (fun _ => Tromino.I.cells) := by
  rw [a.fixed_eq]
  simp only [Pattern.fixedRegion,Finset.mem_biUnion,Atom.prefill_mem,Atom.kind_eq]

/-- The geometric cell predicate refers to actual prescribed trominoes. -/
theorem filledAt_iff (i : Fin 24) (c : Cell) :
    FilledAt i c ↔ ∃ p ∈ motif i, c ∈ p.cells (fun _ => Tromino.I.cells) := by
  constructor
  · rintro ⟨entry,he,hc⟩
    obtain ⟨p,hp,hpc⟩ := (entry.1.fixed_mem _).mp hc
    refine ⟨p.shift entry.2,List.mem_flatMap.mpr
      ⟨entry,he,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,?_⟩
    have shifted := (Placement.mem_shift_cells (fun _ => Tromino.I.cells) entry.2 p
      (Cell.sub c entry.2)).mpr hpc
    have cancel : Cell.add entry.2 (Cell.sub c entry.2) = c := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel] at shifted
  · rintro ⟨q,hq,hqc⟩
    obtain ⟨entry,he,shiftedMember⟩ := List.mem_flatMap.mp hq
    change q ∈ entry.1.motif.map (fun p => p.shift entry.2) at shiftedMember
    obtain ⟨p,baseMember,shiftEq⟩ := List.mem_map.mp shiftedMember
    subst q
    refine ⟨entry,he,(entry.1.fixed_mem _).mpr ⟨p,baseMember,?_⟩⟩
    apply (Placement.mem_shift_cells (fun _ => Tromino.I.cells) entry.2 p (Cell.sub c entry.2)).mp
    have cancel : Cell.add entry.2 (Cell.sub c entry.2) = c := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel]

end LeanTrominoes.CompletionPattern.IBricks
