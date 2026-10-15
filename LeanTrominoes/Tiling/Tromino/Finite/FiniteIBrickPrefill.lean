/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteICompletionGuards

/-! # Finite brick preplacements supply the local soundness barriers -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

def prefill (palette : Cell → Fin 24) (locations : List Cell) : List (Placement Unit) :=
  locations.flatMap fun location => (motif (palette location)).map fun p => p.shift (origin location)

def prescribed (palette : Cell → Fin 24) (locations : List Cell) : Set (Finset Cell) :=
  {f | ∃ location∈locations, ∃ p∈motif (palette location),
    f=(p.shift (origin location)).cells (fun _ => Tromino.I.cells)}

theorem prescribed_eq_footprints (palette : Cell → Fin 24) (locations : List Cell) :
    prescribed palette locations=
      (((prefill palette locations).map fun p => p.cells (fun _ => Tromino.I.cells)).toFinset : Set (Finset Cell)) := by
  ext f
  simp only [prescribed,prefill,Set.mem_setOf_eq,Finset.mem_coe,List.mem_toFinset,List.mem_map,List.mem_flatMap]
  constructor
  · rintro ⟨location,member,p,hp,rfl⟩
    exact ⟨p.shift (origin location),⟨location,member,p,hp,rfl⟩,rfl⟩
  · rintro ⟨q,⟨location,member,p,hp,rfl⟩,rfl⟩
    exact ⟨location,member,p,hp,rfl⟩

theorem prescribed_subset_global (palette : Cell → Fin 24) (locations : List Cell) :
    prescribed palette locations ⊆ globalPrescribed palette := by
  rintro f ⟨location,_,p,hp,rfl⟩
  exact ⟨location,p,hp,rfl⟩

private theorem filled_retained (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (retained : prescribed palette locations ⊆ completed)
    {location c : Cell} (member : location∈locations) (filled : FilledAt (palette location) c) :
    ∃ f∈globalPrescribed palette, f∈completed ∧ Cell.add (origin location) c∈f := by
  obtain ⟨p,hp,covers⟩ := (filledAt_iff _ _).mp filled
  refine ⟨(p.shift (origin location)).cells (fun _ => Tromino.I.cells),⟨location,p,hp,rfl⟩,
    retained ⟨location,member,p,hp,rfl⟩,?_⟩
  exact (Placement.mem_shift_cells (fun _ => Tromino.I.cells) (origin location) p c).mpr covers

theorem own_retained (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (retained : prescribed palette locations ⊆ completed)
    {location : Cell} (member : location∈locations) {entry : Atom × Cell}
    (he : entry∈layout (palette location)) : atomPrescribed location entry ⊆ completed := by
  rintro f ⟨p,hp,rfl⟩
  apply retained
  refine ⟨location,member,p.shift entry.2,List.mem_flatMap.mpr
    ⟨entry,he,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,?_⟩
  exact (shift_cells_twice p _ _).symm

/-- The I-tromino conflict certificate uses only its own brick's preplacements. -/
theorem barrier_retained (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (retained : prescribed palette locations ⊆ completed)
    {location : Cell} (own : location∈locations)
    {entry : Atom × Cell} (he : entry∈layout (palette location)) :
    BarrierRetained palette completed location entry := by
  intro c hc
  obtain ⟨p,hp,covers⟩ := (entry.1.fixed_mem c).mp hc
  exact ⟨_,atom_prescribed palette location he hp,
    own_retained palette locations retained own he ⟨p,hp,rfl⟩,
    (Placement.mem_shift_cells (fun _ => Tromino.I.cells) (atomOffset location entry) p c).mpr covers⟩
end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
