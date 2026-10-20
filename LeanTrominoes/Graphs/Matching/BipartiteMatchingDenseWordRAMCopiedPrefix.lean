/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRowMemory
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopyMemory

/-! # A copied prefix row has exactly the source path's entries -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def copiedPrefixMemory (input : Input) (memory : Nat → Nat) (source target : Fin input.1) (count : Nat) :=
  let a := Layout.ofInput input
  copyMemory memory (a.base Slot.rowLeft+source.val*input.1) (a.base Slot.rowRight+source.val*input.1)
    (a.base Slot.rowLeft+target.val*input.1) (a.base Slot.rowRight+target.val*input.1) count

theorem copiedPrefixMemory_spec (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat)
    (rep : MemoryRep input matching paths memory) (bound : PathsBound input paths)
    (source target : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1))
    (marked : paths source=some prior) (unseen : paths target=none) :
    MemoryRep input matching paths (copiedPrefixMemory input memory source target prior.length) ∧
    (∀ j : Fin prior.length, copiedPrefixMemory input memory source target prior.length
      ((Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+j.val))=(prior.get j).1.val) ∧
    (∀ j : Fin prior.length, copiedPrefixMemory input memory source target prior.length
      ((Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j.val))=(prior.get j).2.val) := by
  let a := Layout.ofInput input
  have different : source.val≠target.val := by
    intro same
    have eq : source=target := Fin.ext same
    subst source
    simp [unseen] at marked
  have colBound (j : Nat) (hj : j<prior.length) : j< input.1 := hj.trans_le (bound source prior marked)
  have targets (i k : Nat) (hi : i<prior.length) (hk : k<prior.length) :
      a.base Slot.rowLeft+target.val*input.1+i≠a.base Slot.rowRight+target.val*input.1+k := by
    simpa only [Nat.add_assoc] using a.disjoint Slot.rowLeft Slot.rowRight (by decide)
      (target.val*input.1+i) (target.val*input.1+k)
      (row_index_bound target.isLt (colBound i hi)) (row_index_bound target.isLt (colBound k hk))
  have sourceL (i k : Nat) (hi : i<prior.length) (hk : k<prior.length) :
      a.base Slot.rowLeft+source.val*input.1+i≠a.base Slot.rowLeft+target.val*input.1+k ∧
      a.base Slot.rowLeft+source.val*input.1+i≠a.base Slot.rowRight+target.val*input.1+k := by
    constructor
    · intro same
      have same' : source.val*input.1+i=target.val*input.1+k := by omega
      exact row_index_disjoint (colBound i hi) (colBound k hk) different same'
    · simpa only [Nat.add_assoc] using a.disjoint Slot.rowLeft Slot.rowRight (by decide)
        (source.val*input.1+i) (target.val*input.1+k)
        (row_index_bound source.isLt (colBound i hi)) (row_index_bound target.isLt (colBound k hk))
  have sourceR (i k : Nat) (hi : i<prior.length) (hk : k<prior.length) :
      a.base Slot.rowRight+source.val*input.1+i≠a.base Slot.rowLeft+target.val*input.1+k ∧
      a.base Slot.rowRight+source.val*input.1+i≠a.base Slot.rowRight+target.val*input.1+k := by
    constructor
    · simpa only [Nat.add_assoc] using a.disjoint Slot.rowRight Slot.rowLeft (by decide)
        (source.val*input.1+i) (target.val*input.1+k)
        (row_index_bound source.isLt (colBound i hi)) (row_index_bound target.isLt (colBound k hk))
    · intro same
      have same' : source.val*input.1+i=target.val*input.1+k := by omega
      exact row_index_disjoint (colBound i hi) (colBound k hk) different same'
  constructor
  · apply rep.unseenRowFrame input matching paths memory _ bound target unseen
    intro address outside
    apply copyMemory_frame
    intro j hj
    simpa only [Nat.add_assoc] using outside j (colBound j hj)
  · constructor
    · intro j
      have copied := copyMemory_left memory (a.base Slot.rowLeft+source.val*input.1) (a.base Slot.rowRight+source.val*input.1)
        (a.base Slot.rowLeft+target.val*input.1) (a.base Slot.rowRight+target.val*input.1)
        prior.length prior.length j.val (le_refl _) j.isLt targets sourceL
      simpa only [a,Nat.add_assoc,copiedPrefixMemory] using copied.trans (by simpa only [a,Nat.add_assoc] using rep.rowLeft source prior marked j)
    · intro j
      have copied := copyMemory_right memory (a.base Slot.rowLeft+source.val*input.1) (a.base Slot.rowRight+source.val*input.1)
        (a.base Slot.rowLeft+target.val*input.1) (a.base Slot.rowRight+target.val*input.1)
        prior.length prior.length j.val (le_refl _) j.isLt targets sourceR
      simpa only [a,Nat.add_assoc,copiedPrefixMemory] using copied.trans (by simpa only [a,Nat.add_assoc] using rep.rowRight source prior marked j)

end LeanTrominoes.BipartiteMatching.DenseWordRAM
