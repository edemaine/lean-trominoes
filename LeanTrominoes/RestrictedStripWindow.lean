/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripWindowCandidates
import LeanTrominoes.TranslationTiling

/-! # Finite-window constraints for orientation-restricted strip tilings -/

namespace LeanTrominoes.RestrictedStripWindow
open PolyominoStripWindow

def ValidWith {ι : Type*} (tiles : ι → Polyomino) (allowed : ι → SquareSymmetry → Prop)
    {height bound : Nat} (window : Window ι height bound) : Prop :=
  ValidWindow tiles window ∧ ∀ slot, window 0 slot = true → allowed slot.1 slot.2.1

theorem satisfiable_of_tileable {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (allowed : ι → SquareSymmetry → Prop) (bounded : Bounded tiles bound) (tiled : TileableWith tiles (horizontalStrip height) (fun p => allowed p.kind p.symmetry)) :
    LocalWindow.Satisfiable (2*bound) (ValidWith (height := height) tiles allowed) := by
  classical
  obtain ⟨ps,ht,legal⟩ := tiled
  let configuration : Int → Column ι height bound := fun x slot => decide (placement x slot ∈ ps)
  refine ⟨configuration,?_⟩
  intro x
  constructor
  · constructor
    · intro slot selected c hc
      have hp : placement x slot ∈ ps := by simpa [LocalWindow.windowAt,configuration] using selected
      have shifted := ht.tilesInside (placement x slot) hp (Cell.add (x,0) c)
        ((mem_placement_shift tiles x slot c).mpr hc)
      simpa [horizontalStrip,Cell.add] using shifted
    · intro y
      obtain ⟨p,⟨hp,hpc⟩,unique⟩ := ht.uniqueCover (x+bound,(y.val : Int)) (by constructor <;> omega)
      obtain ⟨a,eq⟩ := covering_candidate bounded p x y hpc
      have selected : LocalWindow.windowAt (2*bound) configuration x a.1 a.2 = true := by
        change decide (candidatePlacement x a ∈ ps) = true
        simpa [eq] using hp
      have covers := (candidate_cover_iff tiles x a y.val).mp (by rwa [eq])
      refine ⟨a,⟨selected,covers⟩,?_⟩
      rintro b ⟨hb,hbc⟩
      apply candidatePlacement_injective x
      rw [eq]
      apply unique
      constructor
      · simpa [LocalWindow.windowAt,configuration,candidatePlacement] using hb
      · exact (candidate_cover_iff tiles x b y.val).mpr hbc
  · intro slot selected
    exact legal _ (by simpa [LocalWindow.windowAt,configuration] using selected)

theorem tileable_of_satisfiable {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (allowed : ι → SquareSymmetry → Prop) (bounded : Bounded tiles bound)
    (satisfiable : LocalWindow.Satisfiable (2*bound) (ValidWith (height := height) tiles allowed)) :
    TileableWith tiles (horizontalStrip height) (fun p => allowed p.kind p.symmetry) := by
  obtain ⟨configuration,validWith⟩ := satisfiable
  have valid := fun x => (validWith x).1
  let ps : Set (Placement ι) := {p | ∃ x slot, configuration x slot = true ∧ p = placement x slot}
  refine ⟨ps,⟨?_,?_⟩,?_⟩
  · rintro p ⟨x,slot,selected,rfl⟩ c hc
    have inside := (valid x).1 slot (by simpa [LocalWindow.windowAt] using selected)
    let relative : Cell := (c.1-x,c.2)
    have eq : Cell.add (x,0) relative = c := by simp [relative,Cell.add]
    have covers : relative ∈ (placement 0 slot).cells tiles := by
      apply (mem_placement_shift tiles x slot relative).mp
      rwa [eq]
    exact inside relative covers
  · intro c hc
    let x := c.1-(bound : Int)
    let y : Fin height := ⟨c.2.toNat,by have := hc.1; have := hc.2; omega⟩
    have row : (y.val : Int) = c.2 := by dsimp [y]; have := hc.1; omega
    have cell_eq : (x+bound,(y.val : Int)) = c := by simp [x,row]
    obtain ⟨a,⟨ha,hac⟩,unique⟩ := (valid x).2 y
    have covers : c ∈ (candidatePlacement x a).cells tiles := by
      rw [← cell_eq]
      exact (candidate_cover_iff tiles x a y.val).mpr hac
    refine ⟨candidatePlacement x a,⟨?_,covers⟩,?_⟩
    · exact ⟨x+a.1.val,a.2,ha,rfl⟩
    · rintro p ⟨⟨z,slot,hselected,peq⟩,hpc⟩
      obtain ⟨b,beq⟩ := covering_candidate bounded p x y (by rwa [cell_eq])
      have same := candidate_eq_of_placement (beq.trans peq)
      have selected : LocalWindow.windowAt (2*bound) configuration x b.1 b.2 = true := by
        simpa only [LocalWindow.windowAt,same.1,same.2] using hselected
      have covers := (candidate_cover_iff tiles x b y.val).mp (by rwa [beq,cell_eq])
      have eq := unique b ⟨selected,covers⟩
      exact beq.symm.trans (congrArg (candidatePlacement x) eq)

  · rintro p ⟨x,slot,selected,rfl⟩
    exact (validWith x).2 slot (by simpa [LocalWindow.windowAt] using selected)

/-- Arbitrary finite tile footprints reduce to a finite overlap graph. -/
theorem tileable_iff_cycle {ι : Type*} [Fintype ι] {tiles : ι → Polyomino} {height bound : Nat}
    (allowed : ι → SquareSymmetry → Prop) (bounded : Bounded tiles bound) :
    TileableWith tiles (horizontalStrip height) (fun p => allowed p.kind p.symmetry) ↔
      FiniteState.HasCycle (LocalWindow.Transition (ValidWith (height := height) (bound := bound) tiles allowed)) := by
  classical
  rw [← LocalWindow.satisfiable_iff_cycle]
  exact ⟨satisfiable_of_tileable allowed bounded,tileable_of_satisfiable allowed bounded⟩

end LeanTrominoes.RestrictedStripWindow
