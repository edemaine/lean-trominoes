/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLStripCut

/-! # Every prescribed tile of a finite brick band lies inside its core -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 0
set_option maxRecDepth 65536

theorem motif_core_bounds : ∀ i : Fin 24, ∀ p ∈ motif i, ∀ c ∈ p.cells (fun _ => Tromino.L.cells),
    0 ≤ c.2 ∧ c.2 ≤ 36 ∧ (c.2 = 0 → 6 ≤ c.1%12) ∧ (c.2 = 36 → c.1%12 < 6) := by
  decide +kernel

theorem band_prescribed_inside (palette : Cell → Fin 24) (count : Int)
    (f : Finset Cell) (hf : f ∈ bandPrescribed palette count) :
    ∀ c ∈ f, c ∈ StripCaps.coreBand .L (36*count) := by
  obtain ⟨o,hband,hf⟩ := hf
  obtain ⟨p,hp,eq⟩ := hf
  have inMotif : p.shift o.entry.2 ∈ motif (palette o.location) := by
    apply List.mem_flatMap.mpr
    exact ⟨o.entry,o.member,List.mem_map.mpr ⟨p,hp,rfl⟩⟩
  intro c hc
  rw [eq] at hc
  have shifted : (p.shift (atomOffset o.location o.entry)).cells (fun _ => Tromino.L.cells) =
      ((p.shift o.entry.2).shift (origin o.location)).cells (fun _ => Tromino.L.cells) := by
    congr 1
    simp [Placement.shift,atomOffset,Cell.add,Int.add_assoc,Int.add_comm,Int.add_left_comm]
  rw [shifted,Placement.shift_cells_image] at hc
  obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
  have bounds := motif_core_bounds (palette o.location) _ inMotif d hd
  unfold InBand at hband
  change 0 ≤ (Cell.add (origin o.location) d).2 ∧ _
  simp only [StripCaps.coreBand,Set.mem_setOf_eq,StripCaps.width,Cell.add,origin]
  omega

end LeanTrominoes.CompletionPattern.LBricks
