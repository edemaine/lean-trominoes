/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWorklistRAM
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Magnitude bounds for reachable Horn worklist states

Counters never increase during propagation. The queue and the total number of
processed queue cells are bounded by the rule count, including duplicate
premise occurrences. These are value and storage bounds, not a RAM-program
simulation.
-/
namespace LeanTrominoes.Horn.Worklist
variable {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] [DecidableEq R] [Enumeration R]

omit [Fintype A] [Fintype R] [Enumeration R] in
theorem advance_counter_le (buckets : A → List R) (head : R → A) (s : State A R) (r : R) :
    (advance buckets head s).counter r ≤ s.counter r := by
  unfold advance
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · exact (by simp only [tick_counter]; omega)

omit [Fintype A] [Fintype R] [Enumeration R] in
theorem index_counter_le (edges : List (A × R)) (r : R) :
    (index edges).counter r ≤ edges.length := by
  rw [index_counter]
  exact List.countP_le_length

theorem advance_potential_le (buckets : A → List R) (head : R → A) (s : State A R) :
    potential (advance buckets head s) ≤ potential s := by
  by_cases empty : s.queue=[]
  · simp [advance,empty]
  · have := potential_advance buckets head s empty
    omega

/-- Every finite transition prefix has bounded counters and queue length. -/
theorem reachable_word_bounds (edges : List (A × R)) (head : R → A) (s : State A R)
    (reachable : Relation.ReflTransGen (fun before after => after = advance (index edges).bucket head before)
      (initial edges head) s) :
    (∀ r, s.counter r ≤ edges.length) ∧ s.queue.length ≤ Fintype.card R := by
  have invariant : (∀ r, s.counter r ≤ edges.length) ∧ potential s ≤ Fintype.card R := by
    induction reachable with
    | refl => exact ⟨index_counter_le edges, by rw [initial_potential]⟩
    | @tail middle last trace step ih =>
      subst last
      exact ⟨fun r => (advance_counter_le _ _ _ r).trans (ih.1 r),
        (advance_potential_le _ _ _).trans ih.2⟩
  exact ⟨invariant.1, (Nat.le_add_right _ _).trans invariant.2⟩

/-- Each nonempty queue step consumes one unit of potential. This also bounds
allocation by a linked implementation that allocates a rule's ready cell once. -/
theorem nonempty_steps_bound (edges : List (A × R)) (head : R → A) (steps : ℕ)
    (states : Fin (steps+1) → State A R) (start : states 0 = initial edges head)
    (next : ∀ i : Fin steps, states i.succ = advance (index edges).bucket head (states i.castSucc))
    (nonempty : ∀ i : Fin steps, (states i.castSucc).queue ≠ []) :
    steps ≤ Fintype.card R := by
  have telescope : ∀ i : Fin (steps+1), potential (states i)+i.val = Fintype.card R := by
    intro i
    induction h : i.val using Nat.strong_induction_on generalizing i with
    | h k ih =>
      by_cases zero : k=0
      · have equal : i=0 := Fin.ext (h.trans zero)
        simp only [equal,start,initial_potential,zero,Nat.add_zero]
      · have positive : 0<k := by omega
        let j : Fin steps := ⟨k-1,by have := i.isLt; omega⟩
        have prev := ih (k-1) (by omega) j.castSucc rfl
        have same : i=j.succ := Fin.ext (by simp [j]; omega)
        have drop := potential_advance (index edges).bucket head (states j.castSucc) (nonempty j)
        rw [← next j] at drop
        rw [same]
        omega
  have last := telescope (Fin.last steps)
  simp only [Fin.val_last] at last
  omega

/-- All counters and the queue length fit any word size above the binary
length of the rule-and-occurrence count. -/
theorem reachable_fits (edges : List (A × R)) (head : R → A) (s : State A R)
    (reachable : Relation.ReflTransGen (fun before after => after = advance (index edges).bucket head before)
      (initial edges head) s) (w : ℕ) (width : WordBounds.bits (edges.length+Fintype.card R)≤w) :
    (∀ r, ComplexityAbstract.RAM.Fits w (s.counter r : ℤ)) ∧
      ComplexityAbstract.RAM.Fits w (s.queue.length : ℤ) := by
  obtain ⟨counters,queue⟩ := reachable_word_bounds edges head s reachable
  constructor
  · intro r
    apply WordBounds.fits_mono width (WordBounds.fits_of_natAbs_le _ _ ?_)
    simpa using (counters r).trans (Nat.le_add_right edges.length (Fintype.card R))
  · apply WordBounds.fits_mono width (WordBounds.fits_of_natAbs_le _ _ ?_)
    simpa using queue.trans (Nat.le_add_left (Fintype.card R) edges.length)

end LeanTrominoes.Horn.Worklist
