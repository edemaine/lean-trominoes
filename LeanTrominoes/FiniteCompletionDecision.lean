/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteICompletionDecision
import LeanTrominoes.FiniteLCompletionDecision

/-! # The decidability part of Theorem 5.12

Both free trominoes admit a finite box-cover characterization of plane
completion. This file does not assert the separate NP-completeness clause.
-/
namespace LeanTrominoes.Tromino.FiniteWitness

def decideCompletion (t : Tromino) (prefill : Finset (Finset Cell)) : Bool :=
  check t (box (radius prefill)) prefill

theorem decideCompletion_correct (t : Tromino) (prefill : Finset (Finset Cell)) :
    decideCompletion t prefill=true ↔ t.Completable Set.univ (prefill : Set (Finset Cell)) := by
  cases t
  · exact FiniteI.decideCompletion_correct prefill
  · exact FiniteL.decideCompletion_correct prefill

/-- A computational decision instance, obtained from the executable search. -/
def completionDecidable (t : Tromino) (prefill : Finset (Finset Cell)) :
    Decidable (t.Completable Set.univ (prefill : Set (Finset Cell))) :=
  decidable_of_iff (decideCompletion t prefill=true) (decideCompletion_correct t prefill)

theorem completion_of_witness (t : Tromino) {r : Nat} {prefill tiles : Finset (Finset Cell)}
    (h : Valid t (box r) prefill tiles) :
    t.Completable Set.univ (prefill : Set (Finset Cell)) := by
  cases t
  · exact FiniteI.completion_of_witness h
  · exact FiniteL.completion_of_witness h

theorem box_card (r : Nat) : (box r).card=(2*r+1)^2 := by
  have injective : Function.Injective (fun k : Nat => (k:Int)-(r:Int)) := by
    intro a b h
    have equal : (a:Int)=(b:Int) := by dsimp at h; omega
    exact Int.ofNat_inj.mp equal
  have count : (interval r).card=2*r+1 := by
    rw [interval,Finset.card_image_of_injective _ injective,Finset.card_range]
  calc
    (box r).card=(interval r).card*(interval r).card := Finset.card_product _ _
    _ = (2*r+1)^2 := by rw [count,pow_two]

/-- A finite certificate has a number of tiles bounded by the box area. -/
theorem completion_iff_bounded_witness (t : Tromino) (prefill : Finset (Finset Cell)) :
    t.Completable Set.univ (prefill : Set (Finset Cell)) ↔
    ∃ tiles, Valid t (box (radius prefill)) prefill tiles ∧
      tiles.card≤(2*radius prefill+1)^2 := by
  rw [← box_card]
  cases t
  · exact FiniteI.completion_iff_bounded_witness prefill
  · exact FiniteL.completion_iff_bounded_witness prefill

end LeanTrominoes.Tromino.FiniteWitness
