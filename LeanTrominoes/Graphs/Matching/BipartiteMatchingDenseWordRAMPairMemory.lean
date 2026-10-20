/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitialize

/-! # Two partner-array stores implement one pair update -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def pairMemory (input : Input) (memory : Nat → Nat) (l : Fin input.1) (r : Fin input.2.1) :=
  Function.update
    (Function.update memory ((Layout.ofInput input).base Slot.partnerLeft+l.val) (r.val+1))
    ((Layout.ofInput input).base Slot.partnerRight+r.val) (l.val+1)

theorem pairMemory_represents (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat)
    (rep : MemoryRep input matching paths memory) (bound : PathsBound input paths)
    (l : Fin input.1) (r : Fin input.2.1) :
    MemoryRep input (BipartiteMatching.pair matching l r) paths (pairMemory input memory l r) := by
  have unchanged (slot : Slot) (i : Nat) (within : i<(Layout.ofInput input).length slot)
      (different : slot≠Slot.partnerLeft ∧ slot≠Slot.partnerRight) :
      pairMemory input memory l r ((Layout.ofInput input).base slot+i)=memory ((Layout.ofInput input).base slot+i) := by
    simp only [pairMemory,
      Function.update_of_ne ((Layout.ofInput input).disjoint slot Slot.partnerRight different.2 i r.val within r.isLt),
      Function.update_of_ne ((Layout.ofInput input).disjoint slot Slot.partnerLeft different.1 i l.val within l.isLt)]
  constructor
  · intro i; rw [unchanged Slot.edgeLeft i.val i.isLt (by decide)]; exact rep.edgeLeft i
  · intro i; rw [unchanged Slot.edgeRight i.val i.isLt (by decide)]; exact rep.edgeRight i
  · intro a
    have cross := (Layout.ofInput input).disjoint Slot.partnerLeft Slot.partnerRight (by decide) a.val r.val a.isLt r.isLt
    simp only [pairMemory,Function.update_of_ne cross,BipartiteMatching.pair]
    by_cases same : a=l
    · subst a; simp [optionCode]
    · have different : (Layout.ofInput input).base Slot.partnerLeft+a.val≠(Layout.ofInput input).base Slot.partnerLeft+l.val := by
        intro eq; exact same (Fin.ext (by omega))
      simpa [Function.update_of_ne same,Function.update_of_ne different] using rep.partnerLeft a
  · intro b
    by_cases same : b=r
    · subst b; simp [pairMemory,BipartiteMatching.pair,optionCode]
    · have different : (Layout.ofInput input).base Slot.partnerRight+b.val≠(Layout.ofInput input).base Slot.partnerRight+r.val := by
        intro eq; exact same (Fin.ext (by omega))
      have cross := (Layout.ofInput input).disjoint Slot.partnerRight Slot.partnerLeft (by decide) b.val l.val b.isLt l.isLt
      simpa [pairMemory,BipartiteMatching.pair,Function.update_of_ne same,Function.update_of_ne different,
        Function.update_of_ne cross] using rep.partnerRight b
  · intro a; rw [unchanged Slot.lengths a.val a.isLt (by decide)]; exact rep.lengths a
  · intro a prior marked j
    have jbound : j.val< input.1 := by have := bound a prior marked; have := j.isLt; omega
    rw [unchanged Slot.rowLeft (a.val*input.1+j.val) (row_index_bound a.isLt jbound) (by decide)]
    exact rep.rowLeft a prior marked j
  · intro a prior marked j
    have jbound : j.val< input.1 := by have := bound a prior marked; have := j.isLt; omega
    rw [unchanged Slot.rowRight (a.val*input.1+j.val) (row_index_bound a.isLt jbound) (by decide)]
    exact rep.rowRight a prior marked j

end LeanTrominoes.BipartiteMatching.DenseWordRAM
