/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopiedPrefix

/-! # Appending the discovery edge and exposing the finished path row -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def extendedPrefixMemory (input : Input) (memory : Nat → Nat) (source target : Fin input.1)
    (count : Nat) (edge : Fin input.1 × Fin input.2.1) : Nat → Nat :=
  let copied := copiedPrefixMemory input memory source target count
  let left := Function.update copied ((Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+count)) edge.1.val
  Function.update left ((Layout.ofInput input).base Slot.rowRight+(target.val*input.1+count)) edge.2.val

theorem extendedPrefixMemory_spec (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (memory : Nat → Nat)
    (rep : MemoryRep input matching paths memory) (bound : PathsBound input paths)
    (source target : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1))
    (marked : paths source=some prior) (unseen : paths target=none)
    (edge : Fin input.1 × Fin input.2.1) (lengthBound : prior.length+1≤ input.1) :
    MemoryRep input matching (Function.update paths target (some (prior++[edge])))
      (Function.update (extendedPrefixMemory input memory source target prior.length edge)
        ((Layout.ofInput input).base Slot.lengths+target.val) (prior.length+2)) := by
  obtain ⟨copiedRep,copiedLeft,copiedRight⟩ := copiedPrefixMemory_spec input matching paths memory rep bound source target prior marked unseen
  have lastBound : prior.length< input.1 := by omega
  have cross (i j : Nat) (hi : i< input.1) (hj : j< input.1) :
      (Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+i)≠(Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j) :=
    (Layout.ofInput input).disjoint Slot.rowLeft Slot.rowRight (by decide) _ _ (row_index_bound target.isLt hi) (row_index_bound target.isLt hj)
  have extendedRep : MemoryRep input matching paths (extendedPrefixMemory input memory source target prior.length edge) := by
    apply copiedRep.unseenRowFrame input matching paths _ _ bound target unseen
    intro address outside
    have different := outside prior.length lastBound
    simp only [extendedPrefixMemory,Function.update_of_ne different.2,Function.update_of_ne different.1]
  have left : ∀ j : Fin (prior++[edge]).length,
      extendedPrefixMemory input memory source target prior.length edge
        ((Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+j.val))=((prior++[edge]).get j).1.val := by
    intro j
    have jbound : j.val< input.1 := by have := j.isLt; simp only [List.length_append,List.length_singleton] at this; omega
    have rightDifferent := cross j.val prior.length jbound lastBound
    by_cases before : j.val<prior.length
    · have lastDifferent : (Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+j.val)≠(Layout.ofInput input).base Slot.rowLeft+(target.val*input.1+prior.length) := by omega
      simp only [extendedPrefixMemory,Function.update_of_ne rightDifferent,Function.update_of_ne lastDifferent]
      simpa [List.get_eq_getElem,List.getElem_append_left before] using copiedLeft ⟨j.val,before⟩
    · have equal : j.val=prior.length := by have := j.isLt; simp only [List.length_append,List.length_singleton] at this; omega
      simp [extendedPrefixMemory,Function.update_of_ne (cross prior.length prior.length lastBound lastBound),equal,List.get_eq_getElem]
  have right : ∀ j : Fin (prior++[edge]).length,
      extendedPrefixMemory input memory source target prior.length edge
        ((Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j.val))=((prior++[edge]).get j).2.val := by
    intro j
    have jbound : j.val< input.1 := by have := j.isLt; simp only [List.length_append,List.length_singleton] at this; omega
    by_cases before : j.val<prior.length
    · have lastDifferent : (Layout.ofInput input).base Slot.rowRight+(target.val*input.1+j.val)≠(Layout.ofInput input).base Slot.rowRight+(target.val*input.1+prior.length) := by omega
      have leftDifferent := Ne.symm (cross prior.length j.val lastBound jbound)
      simp only [extendedPrefixMemory,Function.update_of_ne lastDifferent,Function.update_of_ne leftDifferent]
      simpa [List.get_eq_getElem,List.getElem_append_left before] using copiedRight ⟨j.val,before⟩
    · have equal : j.val=prior.length := by have := j.isLt; simp only [List.length_append,List.length_singleton] at this; omega
      simp [extendedPrefixMemory,equal,List.get_eq_getElem]
  have activated := extendedRep.activatePath input matching paths _ bound target (prior++[edge]) (by simpa using lengthBound) left right
  simpa only [List.length_append,List.length_singleton,Nat.add_assoc,Nat.reduceAdd] using activated

end LeanTrominoes.BipartiteMatching.DenseWordRAM
