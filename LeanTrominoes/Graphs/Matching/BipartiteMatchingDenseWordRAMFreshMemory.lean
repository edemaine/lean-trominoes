/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMFresh
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMExtendedPrefix

/-! # Exact memory effects of a fresh discovery's primitive instructions -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.n Reg.m Reg.edges Reg.left Reg.right Reg.mate Reg.length
  Reg.source Reg.target Reg.copyIndex Reg.rowIndex Reg.rowLeft Reg.rowRight Reg.lengths Reg.value Reg.scratch
  fresh1 fresh2 fresh3 fresh4 fresh6 fresh7 fresh8 fresh9 fresh10
  fresh5_fixed fresh5_source fresh5_target fresh5_length
  readState writeState NaturalData.set NaturalData.store

theorem fresh5_memory (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (l target : Fin input.1) (count : Nat)
    (left : d.1 Reg.left=l.val) (mate : d.1 Reg.mate=target.val) (length : d.1 Reg.length=count+1) :
    (fresh5 d).2=copiedPrefixMemory input d.2 l target count := by
  have copied := copy_iterate_memory (fresh4 d) count (by simp [rep.one]) (by simp)
  have leftPtr := rep.pointers Slot.rowLeft
  have rightPtr := rep.pointers Slot.rowRight
  change d.1 Reg.rowLeft=(Layout.ofInput input).base Slot.rowLeft at leftPtr
  change d.1 Reg.rowRight=(Layout.ofInput input).base Slot.rowRight at rightPtr
  simpa [fresh5,length,rep.one,left,mate,rep.n,leftPtr,rightPtr,copiedPrefixMemory] using copied

theorem freshState_memory (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (l target : Fin input.1) (r : Fin input.2.1) (count : Nat)
    (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) (mate : d.1 Reg.mate=target.val)
    (length : d.1 Reg.length=count+1) :
    (freshState d).2=Function.update (extendedPrefixMemory input d.2 l target count (l,r))
      ((Layout.ofInput input).base Slot.lengths+target.val) (count+2) := by
  have leftPtr := rep.pointers Slot.rowLeft
  have rightPtr := rep.pointers Slot.rowRight
  have lengthPtr := rep.pointers Slot.lengths
  change d.1 Reg.rowLeft=(Layout.ofInput input).base Slot.rowLeft at leftPtr
  change d.1 Reg.rowRight=(Layout.ofInput input).base Slot.rowRight at rightPtr
  change d.1 Reg.lengths=(Layout.ofInput input).base Slot.lengths at lengthPtr
  have memory := fresh5_memory input matching paths d rep l target count left mate length
  simp [freshState,extendedPrefixMemory,memory,left,right,mate,length,rep.n,rep.one,leftPtr,rightPtr,lengthPtr]

end LeanTrominoes.BipartiteMatching.DenseWordRAM
