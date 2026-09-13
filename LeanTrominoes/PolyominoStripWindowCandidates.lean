/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripWindow

/-! # Every covering placement has a unique finite window record -/

namespace LeanTrominoes.PolyominoStripWindow

def candidatePlacement {ι : Type*} {height bound : Nat} (x : Int)
    (a : Candidate ι height bound) : Placement ι := placement (x+a.1.val) a.2

theorem candidatePlacement_injective {ι : Type*} {height bound : Nat} (x : Int) :
    Function.Injective (candidatePlacement (ι := ι) (height := height) (bound := bound) x) := by
  intro a b eq
  have hx := congrArg (fun p : Placement ι => p.offset.1) eq
  have cols : a.1 = b.1 := by apply Fin.ext; dsimp [candidatePlacement,placement] at hx; omega
  apply Prod.ext cols
  apply placement_injective (x+a.1.val)
  simpa only [candidatePlacement,cols] using eq

theorem candidatePlacement_shift {ι : Type*} {height bound : Nat} (x : Int)
    (a : Candidate ι height bound) :
    candidatePlacement x a = (placement a.1.val a.2).shift (x,0) := by
  simp [candidatePlacement,placement,Placement.shift,Cell.add]

theorem candidate_cover_iff {ι : Type*} (tiles : ι → Polyomino) {height bound : Nat}
    (x : Int) (a : Candidate ι height bound) (y : Int) :
    (x+bound,y) ∈ (candidatePlacement x a).cells tiles ↔
      ((bound : Int),y) ∈ (placement a.1.val a.2).cells tiles := by
  rw [candidatePlacement_shift]
  simpa [Cell.add] using Placement.mem_shift_cells tiles (x,0) (placement a.1.val a.2) (bound,y)

theorem covering_candidate {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (bounded : Bounded tiles bound) (p : Placement ι) (x : Int) (y : Fin height)
    (covers : (x+bound,(y.val : Int)) ∈ p.cells tiles) :
    ∃ a : Candidate ι height bound, candidatePlacement x a = p := by
  obtain ⟨slot,slot_eq⟩ := covering_slot (height := height) bounded p (by constructor <;> omega) covers
  obtain ⟨q,hq,eq⟩ := (Placement.mem_cells_iff _ _ _).mp covers
  have bounds := act_bounds bounded p.kind hq p.symmetry
  have hx := congrArg Prod.fst eq
  dsimp [Cell.add] at hx
  have lo : 0 ≤ p.offset.1-x := by omega
  have hi : (p.offset.1-x).toNat < 2*bound+1 := by omega
  refine ⟨(⟨(p.offset.1-x).toNat,hi⟩,slot),?_⟩
  have coord : x+((p.offset.1-x).toNat : Int) = p.offset.1 := by omega
  simpa only [candidatePlacement,coord] using slot_eq

/-- The finite record recovered from a placement retains its selected column and slot. -/
theorem candidate_eq_of_placement {ι : Type*} {height bound : Nat} {x z : Int}
    {slot : Slot ι height bound} {a : Candidate ι height bound}
    (eq : candidatePlacement x a = placement z slot) : x+a.1.val = z ∧ a.2 = slot := by
  have col := congrArg (fun p : Placement ι => p.offset.1) eq
  change x+a.1.val = z at col
  exact ⟨col,placement_injective z (by simpa [candidatePlacement,col] using eq)⟩

end LeanTrominoes.PolyominoStripWindow
