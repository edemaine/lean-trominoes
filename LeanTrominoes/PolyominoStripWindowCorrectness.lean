/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PolyominoStripWindowCandidates

/-! # Exact equivalence between strip tilings and finite-window constraints -/

namespace LeanTrominoes.PolyominoStripWindow

theorem satisfiable_of_tileable {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (bounded : Bounded tiles bound) (tiled : Tileable tiles (horizontalStrip height)) :
    LocalWindow.Satisfiable (2*bound) (ValidWindow (height := height) tiles) := by
  classical
  obtain ⟨ps,ht⟩ := tiled
  let configuration : Int → Column ι height bound := fun x slot => decide (placement x slot ∈ ps)
  refine ⟨configuration,?_⟩
  intro x
  constructor
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

theorem tileable_of_satisfiable {ι : Type*} {tiles : ι → Polyomino} {height bound : Nat}
    (bounded : Bounded tiles bound)
    (satisfiable : LocalWindow.Satisfiable (2*bound) (ValidWindow (height := height) tiles)) :
    Tileable tiles (horizontalStrip height) := by
  obtain ⟨configuration,valid⟩ := satisfiable
  let ps : Set (Placement ι) := {p | ∃ x slot, configuration x slot = true ∧ p = placement x slot}
  refine ⟨ps,?_,?_⟩
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

/-- Arbitrary finite tile footprints reduce to a finite overlap graph. -/
theorem tileable_iff_cycle {ι : Type*} [Fintype ι] {tiles : ι → Polyomino} {height bound : Nat}
    (bounded : Bounded tiles bound) :
    Tileable tiles (horizontalStrip height) ↔
      FiniteState.HasCycle (LocalWindow.Transition (ValidWindow (height := height) (bound := bound) tiles)) := by
  classical
  rw [← LocalWindow.satisfiable_iff_cycle]
  exact ⟨satisfiable_of_tileable bounded,tileable_of_satisfiable bounded⟩

end LeanTrominoes.PolyominoStripWindow
