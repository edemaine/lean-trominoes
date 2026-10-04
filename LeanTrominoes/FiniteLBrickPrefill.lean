/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteLCompletionGuards

/-! # Finite brick preplacements supply the local soundness barriers -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.FiniteGuards
open LBricks
set_option maxHeartbeats 2000000

def prefill (palette : Cell → Fin 24) (locations : List Cell) : List (Placement Unit) :=
  locations.flatMap fun location => (motif (palette location)).map fun p => p.shift (origin location)

def prescribed (palette : Cell → Fin 24) (locations : List Cell) : Set (Finset Cell) :=
  {f | ∃ location∈locations, ∃ p∈motif (palette location),
    f=(p.shift (origin location)).cells (fun _ => Tromino.L.cells)}

theorem prescribed_eq_footprints (palette : Cell → Fin 24) (locations : List Cell) :
    prescribed palette locations=
      (((prefill palette locations).map fun p => p.cells (fun _ => Tromino.L.cells)).toFinset : Set (Finset Cell)) := by
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
  refine ⟨(p.shift (origin location)).cells (fun _ => Tromino.L.cells),⟨location,p,hp,rfl⟩,
    retained ⟨location,member,p,hp,rfl⟩,?_⟩
  exact (Placement.mem_shift_cells (fun _ => Tromino.L.cells) (origin location) p c).mpr covers

theorem own_retained (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (retained : prescribed palette locations ⊆ completed)
    {location : Cell} (member : location∈locations) {entry : Atom × Cell}
    (he : entry∈layout (palette location)) : atomPrescribed location entry ⊆ completed := by
  rintro f ⟨p,hp,rfl⟩
  apply retained
  refine ⟨location,member,p.shift entry.2,List.mem_flatMap.mpr
    ⟨entry,he,List.mem_map.mpr ⟨p,hp,rfl⟩⟩,?_⟩
  exact (shift_cells_twice p _ _).symm

/-- One brick and its four diagonal neighbors supply all six atom barriers. -/
theorem barrier_retained (palette : Cell → Fin 24) (locations : List Cell)
    {completed : Set (Finset Cell)} (retained : prescribed palette locations ⊆ completed)
    {location : Cell} (own : location∈locations)
    (neighbors : ∀ delta∈([(0,-1),(1,-1),(-1,1),(0,1)] : List Cell),
      Cell.add location delta∈locations)
    {entry : Atom × Cell} (he : entry∈layout (palette location)) :
    BarrierRetained palette completed location entry := by
  intro c hc
  have reassociate : Cell.add (atomOffset location entry) c=
      Cell.add (origin location) (Cell.add entry.2 c) := by
    apply Prod.ext <;> dsimp [atomOffset,Cell.add] <;> omega
  rw [reassociate]
  rcases Finset.mem_union.mp hc with fixed|extra
  · apply filled_retained palette locations retained own
    refine ⟨entry,he,?_⟩
    have cancel : Cell.sub (Cell.add entry.2 c) entry.2=c := by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel]
  · rcases extra_supplied (palette location) entry he c extra with ownFilled|skin
    · exact filled_retained palette locations retained own ownFilled
    · have covered := external_skin_covered skin
      simp only [Finset.mem_union] at covered
      have supplied (delta : Cell) (member : delta∈([(0,-1),(1,-1),(-1,1),(0,1)] : List Cell))
          (skin : Finset Cell) (supply : ∀ i : Fin 24,∀ d∈skin,FilledAt i d)
          (cover : Cell.add entry.2 c∈skin.image (Cell.add (origin delta))) :
          ∃ f∈globalPrescribed palette, f∈completed ∧
            Cell.add (origin location) (Cell.add entry.2 c)∈f := by
        obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp cover
        obtain ⟨f,hf,retainedF,covers⟩ := filled_retained palette locations retained
          (neighbors delta member) (supply _ d hd)
        refine ⟨f,hf,retainedF,?_⟩
        rw [← eq]
        have associate : Cell.add (origin location) (Cell.add (origin delta) d)=
            Cell.add (origin (Cell.add location delta)) d := by
          rw [origin_add]
          apply Prod.ext <;> dsimp [Cell.add] <;> omega
        rwa [associate]
      rcases covered with ((aboveLeft|aboveRight)|belowLeft)|belowRight
      · apply supplied (0,-1) (by simp) bottomSkin bottom_skin_filled
        simpa [origin] using aboveLeft
      · apply supplied (1,-1) (by simp) bottomSkin bottom_skin_filled
        simpa [origin] using aboveRight
      · apply supplied (-1,1) (by simp) topSkin top_skin_filled
        simpa [origin] using belowLeft
      · apply supplied (0,1) (by simp) topSkin top_skin_filled
        simpa [origin] using belowRight
end LeanTrominoes.CompletionPattern.LBricks.FiniteGuards
