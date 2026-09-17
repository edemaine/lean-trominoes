/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPrefillPeriods
import LeanTrominoes.CylinderArbitraryPeriod

/-! # A singly periodic completion implies a doubly periodic completion

Pumping the cylinder preserves all relative tile neighborhoods and the phase
of the prescribed full-rank periodic prefill.
-/
namespace LeanTrominoes.CompletionPeriodic
set_option maxHeartbeats 2000000

def fieldSupport (t : Tromino) : Finset Cell := (states t).biUnion id

theorem state_mem_support {t : Tromino} (s : State t) {d : Cell} (hd : d ∈ s.val) : d ∈ fieldSupport t :=
  Finset.mem_biUnion.mpr ⟨s.val,s.property,hd⟩

/-- The general pumping step only needs a square-periodic prescribed tile set. -/
theorem pump_completion {t : Tromino} {prescribed completed : Set (Finset Cell)}
    (tiling : t.IsFootprintTiling Set.univ completed) (retained : prescribed ⊆ completed)
    (n : Nat) (prefillPeriod : HasSquarePeriod prescribed (n+1))
    (v : Cell) (nonzero : v ≠ (0,0)) (periodic : HasTranslationPeriod completed v) :
    ∃ completed', t.IsFootprintTiling Set.univ completed' ∧ prescribed ⊆ completed' ∧
      HasIndependentPeriods completed' := by
  classical
  obtain ⟨f,selected⟩ := field_of_tiling tiling
  have coherent := coherent_of_tiling tiling f selected
  have fp := field_period_of_tiling tiling f selected periodic
  obtain ⟨g,u,w,independent,gu,gw,copy⟩ :=
    Cylinder.local_model f v nonzero fp (insert (0,0) (fieldSupport t)) n
  have coherentG : Coherent g := by
    intro c d hd
    obtain ⟨s,hs⟩ := copy c
    have center : g c = f (Cell.add c (Cell.scale (n+1:Int) s)) := by
      simpa [Cell.add] using hs (0,0) (Finset.mem_insert_self _ _)
    have nearby := hs d (Finset.mem_insert_of_mem (state_mem_support (g c) hd))
    have hd' : d ∈ (f (Cell.add c (Cell.scale (n+1:Int) s))).val := by rw [← center]; exact hd
    rw [nearby,center]
    simpa [Cell.add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using
      coherent (Cell.add c (Cell.scale (n+1:Int) s)) d hd'
  refine ⟨Set.range (fieldTile g),field_tiling coherentG,?_,?_⟩
  · intro tile ht
    obtain ⟨p,rfl⟩ := (tiling.tilesInside tile (retained ht)).1
    obtain ⟨s,hs⟩ := copy p.offset
    let z := Cell.scale (n+1:Int) s
    have center : g p.offset = f (Cell.add p.offset z) := by
      simpa [Cell.add,z] using hs (0,0) (Finset.mem_insert_self _ _)
    have shifted : shift (p.cells (fun _ => t.cells)) z ∈ completed :=
      retained ((prefillPeriod _ s).mp ht)
    have covers : Cell.add p.offset z ∈ shift (p.cells (fun _ => t.cells)) z :=
      Finset.mem_image.mpr ⟨p.offset,t.offset_mem_placement_cells p,by ext <;> simp [Cell.add,Int.add_comm]⟩
    obtain ⟨tile,_,unique⟩ := tiling.uniqueCover (Cell.add p.offset z) (by trivial)
    have eq := (unique _ ⟨selected _,fieldTile_contains f _⟩).trans (unique _ ⟨shifted,covers⟩).symm
    refine ⟨p.offset,?_⟩
    apply shift_injective z
    dsimp only
    calc
      shift (fieldTile g p.offset) z = fieldTile f (Cell.add p.offset z) := by
        simp only [fieldTile,center,shift_shift]
      _ = shift (p.cells (fun _ => t.cells)) z := eq
  · refine ⟨u,w,independent,?_⟩
    intro tile i j
    have combined : Cylinder.IsPeriod g (Cell.add (Cell.scale i u) (Cell.scale j w)) := by
      intro c
      rw [show Cell.add c (Cell.add (Cell.scale i u) (Cell.scale j w)) =
        Cell.add (Cell.add c (Cell.scale i u)) (Cell.scale j w) by ext <;> simp [Cell.add,Int.add_assoc],
        Cylinder.period_multiples gw j,Cylinder.period_multiples gu i]
    exact tiling_period_of_field combined tile

/-- For a doubly periodic prefill, any nonzero period of one completion yields
another completion with two independent translation periods. -/
theorem completion_with_two_periods_of_one (t : Tromino) (input : PeriodicTrominoPrefill)
    (rank : (input.occupiedRegion t).IsFullRank) {completed : Set (Finset Cell)}
    (tiling : t.IsFootprintTiling Set.univ completed) (retained : input.prescribed t ⊆ completed)
    (v : Cell) (nonzero : v ≠ (0,0)) (periodic : HasTranslationPeriod completed v) :
    ∃ completed', t.IsFootprintTiling Set.univ completed' ∧ input.prescribed t ⊆ completed' ∧
      HasIndependentPeriods completed' := by
  obtain ⟨n,hn⟩ := prescribed_square_period t input rank
  exact pump_completion tiling retained n hn v nonzero periodic
end LeanTrominoes.CompletionPeriodic
