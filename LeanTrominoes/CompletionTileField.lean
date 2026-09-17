/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionPeriodicExtraction
import LeanTrominoes.CylinderPeriodicModel

/-! # Finite relative-footprint fields for geometric tromino tilings -/
namespace LeanTrominoes.CompletionPeriodic
open TrominoAssignment
set_option maxHeartbeats 1500000

abbrev shift (f : Finset Cell) (v : Cell) : Finset Cell := f.image (Cell.add v)
@[simp] theorem shift_zero (f : Finset Cell) : shift f (0,0) = f := by
  ext c; simp [shift,Cell.add]
theorem shift_shift (f : Finset Cell) (u v : Cell) :
    shift (shift f u) v = shift f (Cell.add u v) := by
  simp only [shift,Finset.image_image]
  congr 1; funext c; ext <;> dsimp [Cell.add] <;> omega
theorem shift_injective (v : Cell) : Function.Injective (fun f : Finset Cell => shift f v) :=
  fun _ _ h => (Finset.image_inj (Cell.add_left_injective v)).mp h

def HasTranslationPeriod (completed : Set (Finset Cell)) (v : Cell) : Prop :=
  ∀ f, f ∈ completed ↔ shift f v ∈ completed

def states (t : Tromino) : Finset (Finset Cell) :=
  (coveringPlacements t (0,0)).image fun p => p.cells (fun _ => t.cells)
abbrev State (t : Tromino) := {f : Finset Cell // f ∈ states t}
abbrev Field (t : Tromino) := Cell → State t

theorem mem_states (t : Tromino) (f : Finset Cell) :
    f ∈ states t ↔ t.IsFootprint f ∧ (0,0) ∈ f := by
  simp only [states,Finset.mem_image,mem_coveringPlacements_iff]
  constructor
  · rintro ⟨p,hp,rfl⟩; exact ⟨⟨p,rfl⟩,hp⟩
  · rintro ⟨⟨p,rfl⟩,hp⟩; exact ⟨p,hp,rfl⟩

def fieldTile {t : Tromino} (f : Field t) (c : Cell) : Finset Cell := shift (f c).val c

theorem fieldTile_legal {t : Tromino} (f : Field t) (c : Cell) : t.IsFootprint (fieldTile f c) :=
  ((mem_states t _).mp (f c).property).1.translate c

theorem fieldTile_contains {t : Tromino} (f : Field t) (c : Cell) : c ∈ fieldTile f c := by
  exact Finset.mem_image.mpr ⟨(0,0),((mem_states t _).mp (f c).property).2,by simp [Cell.add]⟩

def Coherent {t : Tromino} (f : Field t) : Prop :=
  ∀ c d, d ∈ (f c).val → shift (f (Cell.add c d)).val d = (f c).val

theorem coherent_tile_eq {t : Tromino} {f : Field t} (h : Coherent f) (c d : Cell)
    (hd : d ∈ (f c).val) : fieldTile f (Cell.add c d) = fieldTile f c := by
  have eq := congrArg (fun s => shift s c) (h c d hd)
  rw [shift_shift] at eq
  simpa only [fieldTile,show Cell.add d c = Cell.add c d by ext <;> simp [Cell.add,Int.add_comm]] using eq

theorem field_tiling {t : Tromino} {f : Field t} (h : Coherent f) :
    t.IsFootprintTiling Set.univ (Set.range (fieldTile f)) := by
  refine ⟨?_,?_⟩
  · rintro _ ⟨c,rfl⟩; exact ⟨fieldTile_legal f c,by simp⟩
  · intro c _
    refine ⟨fieldTile f c,⟨⟨c,rfl⟩,fieldTile_contains f c⟩,?_⟩
    rintro _ ⟨⟨d,rfl⟩,hc⟩
    obtain ⟨e,he,eq⟩ := Finset.mem_image.mp hc
    change Cell.add d e = c at eq
    rw [← eq]
    exact (coherent_tile_eq h d e he).symm

theorem coherent_of_tiling {t : Tromino} {completed : Set (Finset Cell)}
    (tiling : t.IsFootprintTiling Set.univ completed) (f : Field t)
    (selected : ∀ c, fieldTile f c ∈ completed) : Coherent f := by
  intro c d hd
  obtain ⟨tile,_,unique⟩ := tiling.uniqueCover (Cell.add c d) (by trivial)
  have eq := (unique _ ⟨selected (Cell.add c d),fieldTile_contains f _⟩).trans
    (unique _ ⟨selected c,Finset.mem_image.mpr ⟨d,hd,rfl⟩⟩).symm
  apply shift_injective c
  dsimp only
  rw [shift_shift]
  simpa only [fieldTile,show Cell.add d c = Cell.add c d by ext <;> simp [Cell.add,Int.add_comm]] using eq

theorem field_period_of_tiling {t : Tromino} {completed : Set (Finset Cell)}
    (tiling : t.IsFootprintTiling Set.univ completed) (f : Field t)
    (selected : ∀ c, fieldTile f c ∈ completed) {v : Cell}
    (periodic : HasTranslationPeriod completed v) : Cylinder.IsPeriod f v := by
  intro c
  obtain ⟨tile,_,unique⟩ := tiling.uniqueCover (Cell.add c v) (by trivial)
  have contains : Cell.add c v ∈ shift (fieldTile f c) v :=
    Finset.mem_image.mpr ⟨c,fieldTile_contains f c,by ext <;> simp [Cell.add,Int.add_comm]⟩
  have eq := (unique _ ⟨selected (Cell.add c v),fieldTile_contains f _⟩).trans
    (unique _ ⟨(periodic _).mp (selected c),contains⟩).symm
  apply Subtype.ext
  apply shift_injective (Cell.add c v)
  simpa only [fieldTile,shift_shift] using eq

/-- Every geometric plane tiling induces a finite relative-footprint field. -/
theorem field_of_tiling {t : Tromino} {completed : Set (Finset Cell)}
    (tiling : t.IsFootprintTiling Set.univ completed) :
    ∃ f : Field t, ∀ c, fieldTile f c ∈ completed := by
  classical
  choose cover data unique using fun c => tiling.uniqueCover c (Set.mem_univ c)
  let neg (c : Cell) := Cell.sub (0,0) c
  have legal (c : Cell) : shift (cover c) (neg c) ∈ states t := by
    apply (mem_states t _).mpr
    exact ⟨(tiling.tilesInside _ (data c).1).1.translate _,
      Finset.mem_image.mpr ⟨c,(data c).2,by simp [neg,Cell.add,Cell.sub]⟩⟩
  refine ⟨fun c => ⟨shift (cover c) (neg c),legal c⟩,?_⟩
  intro c
  change shift (shift (cover c) (neg c)) c ∈ completed
  rw [shift_shift,show Cell.add (neg c) c = (0,0) by simp [neg,Cell.add,Cell.sub],shift_zero]
  exact (data c).1

theorem tiling_period_of_field {t : Tromino} {f : Field t} {v : Cell}
    (h : Cylinder.IsPeriod f v) : HasTranslationPeriod (Set.range (fieldTile f)) v := by
  have move (c : Cell) : fieldTile f (Cell.add c v) = shift (fieldTile f c) v := by
    simp only [fieldTile,h c,shift_shift]
  intro tile
  constructor
  · rintro ⟨c,rfl⟩; exact ⟨Cell.add c v,move c⟩
  · rintro ⟨c,hc⟩
    refine ⟨Cell.sub c v,?_⟩
    apply shift_injective v
    dsimp only
    rw [← move,show Cell.add (Cell.sub c v) v = c by ext <;> simp [Cell.add,Cell.sub]]
    exact hc
end LeanTrominoes.CompletionPeriodic
