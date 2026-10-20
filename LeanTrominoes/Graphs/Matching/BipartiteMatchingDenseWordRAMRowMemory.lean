/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitialize

/-! # Writes into an undiscovered path row preserve every represented object -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem MemoryRep.unseenRowFrame (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (before after : Nat → Nat)
    (rep : MemoryRep input matching paths before) (bound : PathsBound input paths)
    (target : Fin input.1) (unseen : paths target=none)
    (frame : ∀ address, (∀ j, j< input.1 →
      address≠(Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+j) ∧
      address≠(Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j)) → after address=before address) :
    MemoryRep input matching paths after := by
  let a := Layout.ofInput input
  have outside (slot : Slot) (i : Nat) (within : i<a.length slot)
      (different : slot≠Slot.rowLeft ∧ slot≠Slot.rowRight) : after (a.base slot+i)=before (a.base slot+i) := by
    apply frame
    intro j hj
    exact ⟨a.disjoint slot Slot.rowLeft different.1 i (target.val*input.1+j) within (row_index_bound target.isLt hj),
      a.disjoint slot Slot.rowRight different.2 i (target.val*input.1+j) within (row_index_bound target.isLt hj)⟩
  constructor
  · intro i; rw [outside Slot.edgeLeft i.val i.isLt (by decide)]; exact rep.edgeLeft i
  · intro i; rw [outside Slot.edgeRight i.val i.isLt (by decide)]; exact rep.edgeRight i
  · intro l; rw [outside Slot.partnerLeft l.val l.isLt (by decide)]; exact rep.partnerLeft l
  · intro r; rw [outside Slot.partnerRight r.val r.isLt (by decide)]; exact rep.partnerRight r
  · intro l; rw [outside Slot.lengths l.val l.isLt (by decide)]; exact rep.lengths l
  · intro l prior marked j
    have different : l≠target := by intro equal; subst l; simp [unseen] at marked
    have jbound : j.val< input.1 := by have := bound l prior marked; have := j.isLt; omega
    rw [frame _ (by
      intro k hk
      constructor
      · intro same
        exact row_index_disjoint jbound hk (fun h => different (Fin.ext h)) (Nat.add_left_cancel same)
      · exact a.disjoint Slot.rowLeft Slot.rowRight (by decide) (l.val*input.1+j.val) (target.val*input.1+k)
          (row_index_bound l.isLt jbound) (row_index_bound target.isLt hk))]
    exact rep.rowLeft l prior marked j
  · intro l prior marked j
    have different : l≠target := by intro equal; subst l; simp [unseen] at marked
    have jbound : j.val< input.1 := by have := bound l prior marked; have := j.isLt; omega
    rw [frame _ (by
      intro k hk
      constructor
      · exact a.disjoint Slot.rowRight Slot.rowLeft (by decide) (l.val*input.1+j.val) (target.val*input.1+k)
          (row_index_bound l.isLt jbound) (row_index_bound target.isLt hk)
      · intro same
        exact row_index_disjoint jbound hk (fun h => different (Fin.ext h)) (Nat.add_left_cancel same))]
    exact rep.rowRight l prior marked j

/-- Only the final length store exposes a freshly prepared row to the search
invariant. All earlier row stores are invisible while its length is zero. -/
theorem MemoryRep.activatePath (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat)
    (rep : MemoryRep input matching paths memory) (bound : PathsBound input paths)
    (target : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1)) (lengthBound : prior.length≤ input.1)
    (left : ∀ j : Fin prior.length, memory ((Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+j.val))=(prior.get j).1.val)
    (right : ∀ j : Fin prior.length, memory ((Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j.val))=(prior.get j).2.val) :
    MemoryRep input matching (Function.update paths target (some prior))
      (Function.update memory ((Layout.ofInput input).base Slot.lengths+target.val) (prior.length+1)) := by
  let a := Layout.ofInput input
  have unchanged (slot : Slot) (i : Nat) (within : i<a.length slot) (different : slot≠Slot.lengths) :
      Function.update memory (a.base Slot.lengths+target.val) (prior.length+1) (a.base slot+i)=memory (a.base slot+i) := by
    exact Function.update_of_ne (a.disjoint slot Slot.lengths different i target.val within target.isLt) _ _
  constructor
  · intro i; rw [unchanged Slot.edgeLeft i.val i.isLt (by decide)]; exact rep.edgeLeft i
  · intro i; rw [unchanged Slot.edgeRight i.val i.isLt (by decide)]; exact rep.edgeRight i
  · intro l; rw [unchanged Slot.partnerLeft l.val l.isLt (by decide)]; exact rep.partnerLeft l
  · intro r; rw [unchanged Slot.partnerRight r.val r.isLt (by decide)]; exact rep.partnerRight r
  · intro l
    by_cases same : l=target
    · subst l; simp [lengthCode]
    · have different : (Layout.ofInput input).base Slot.lengths+l.val≠(Layout.ofInput input).base Slot.lengths+target.val := by
        intro equal; exact same (Fin.ext (by omega))
      simpa [Function.update_of_ne same,Function.update_of_ne different] using rep.lengths l
  · intro l stored marked j
    by_cases same : l=target
    · subst l
      have equal : stored=prior := Option.some.inj (by simpa using marked.symm)
      subst stored
      have jbound : j.val< input.1 := by have := j.isLt; omega
      rw [unchanged Slot.rowLeft (target.val*input.1+j.val) (row_index_bound target.isLt jbound) (by decide)]
      exact left j
    · have old : paths l=some stored := by simpa [Function.update_of_ne same] using marked
      have jbound : j.val< input.1 := by have := bound l stored old; have := j.isLt; omega
      rw [unchanged Slot.rowLeft (l.val*input.1+j.val) (row_index_bound l.isLt jbound) (by decide)]
      exact rep.rowLeft l stored old j
  · intro l stored marked j
    by_cases same : l=target
    · subst l
      have equal : stored=prior := Option.some.inj (by simpa using marked.symm)
      subst stored
      have jbound : j.val< input.1 := by have := j.isLt; omega
      rw [unchanged Slot.rowRight (target.val*input.1+j.val) (row_index_bound target.isLt jbound) (by decide)]
      exact right j
    · have old : paths l=some stored := by simpa [Function.update_of_ne same] using marked
      have jbound : j.val< input.1 := by have := bound l stored old; have := j.isLt; omega
      rw [unchanged Slot.rowRight (l.val*input.1+j.val) (row_index_bound l.isLt jbound) (by decide)]
      exact rep.rowRight l stored old j

end LeanTrominoes.BipartiteMatching.DenseWordRAM
