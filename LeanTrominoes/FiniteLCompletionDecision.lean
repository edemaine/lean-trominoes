/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteLCompletionGrowth
import LeanTrominoes.FiniteCompletionChain
import LeanTrominoes.FiniteCompletionBox

/-! # Deciding completion of a finite L-tromino preplacement -/
namespace LeanTrominoes.Tromino.FiniteL
open RectangleCover FiniteWitness

abbrev CoverState (r : Nat) :=
  {tiles : Finset (Finset Cell) // Covers Tromino.L (-(r:Int),-(r:Int)) (r,r) tiles}

theorem grow_centered {r : Nat} (s : CoverState r) :
    ∃ more, s.val⊆more ∧ Covers Tromino.L (-((r+1:Nat):Int),-((r+1:Nat):Int)) (r+1,r+1) more := by
  obtain ⟨more,sub,h⟩ := grow_box s.property
  refine ⟨more,sub,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one,neg_add,sub_eq_add_neg] using h

noncomputable def nextState {r : Nat} (s : CoverState r) : CoverState (r+1) :=
  ⟨Classical.choose (grow_centered s),(Classical.choose_spec (grow_centered s)).2⟩

theorem nextState_extends {r : Nat} (s : CoverState r) : s.val⊆(nextState s).val :=
  (Classical.choose_spec (grow_centered s)).1

noncomputable def stages {r : Nat} (s : CoverState r) : (n : Nat) → CoverState (r+n)
  | 0 => s
  | n+1 => nextState (stages s n)

theorem complete_state {r : Nat} (s : CoverState r) :
    Tromino.L.Completable Set.univ (s.val : Set (Finset Cell)) := by
  let chain := fun n => (stages s n).val
  have monotone : Monotone chain := by
    apply monotone_nat_of_le_succ
    intro n
    exact nextState_extends (stages s n)
  apply completable_of_increasing_covers Tromino.L chain
    (fun n => (stages s n).property.packing) monotone
  intro c
  let n := c.1.natAbs+c.2.natAbs
  have hx : |c.1|≤((r+n:Nat):Int) := by
    rw [← Int.natCast_natAbs]; dsimp [n]; omega
  have hy : |c.2|≤((r+n:Nat):Int) := by
    rw [← Int.natCast_natAbs]; dsimp [n]; omega
  exact ⟨n,(stages s n).property.covers c
    ⟨(abs_le.mp hx).1,(abs_le.mp hx).2,(abs_le.mp hy).1,(abs_le.mp hy).2⟩⟩

theorem completion_of_witness {r : Nat} {prefill tiles : Finset (Finset Cell)}
    (witness : Valid Tromino.L (box r) prefill tiles) :
    Tromino.L.Completable Set.univ (prefill : Set (Finset Cell)) := by
  have h : Covers Tromino.L (-(r:Int),-(r:Int)) (r,r) tiles := by
    constructor
    · dsimp; omega
    · exact witness.partial
    · intro f hf
      obtain ⟨c,hc,hcf⟩ := ((mem_candidates _ _ _).mp (witness.1 hf)).2
      exact ⟨c,hcf,(mem_box r c).mp hc⟩
    · intro c hc
      exact witness.2.2.2 c ((mem_box r c).mpr hc)
  obtain ⟨completed,tiling,retained⟩ := complete_state (⟨tiles,h⟩ : CoverState r)
  exact ⟨completed,tiling,fun f hf => retained (witness.2.1 hf)⟩

def decideCompletion (prefill : Finset (Finset Cell)) : Bool :=
  check Tromino.L (box (radius prefill)) prefill

theorem decideCompletion_correct (prefill : Finset (Finset Cell)) :
    decideCompletion prefill=true ↔ Tromino.L.Completable Set.univ (prefill : Set (Finset Cell)) := by
  rw [decideCompletion,check_correct]
  constructor
  · rintro ⟨tiles,h⟩; exact completion_of_witness h
  · intro completion
    exact of_completion Tromino.L _ prefill (completion_meets_box Tromino.L prefill completion) completion

theorem completion_iff_bounded_witness (prefill : Finset (Finset Cell)) :
    Tromino.L.Completable Set.univ (prefill : Set (Finset Cell)) ↔
    ∃ tiles, Valid Tromino.L (box (radius prefill)) prefill tiles ∧
      tiles.card≤(box (radius prefill)).card := by
  constructor
  · intro completion
    obtain ⟨tiles,h⟩ := of_completion Tromino.L _ prefill
      (completion_meets_box Tromino.L prefill completion) completion
    exact ⟨tiles,h,h.card_le⟩
  · rintro ⟨tiles,h,_⟩; exact completion_of_witness h

end LeanTrominoes.Tromino.FiniteL
