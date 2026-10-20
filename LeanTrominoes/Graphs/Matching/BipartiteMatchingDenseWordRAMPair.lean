/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPairMemory
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMExecutionFrame

/-! # Eight original instructions write a pair and its inverse -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.left Reg.right Reg.value Reg.scratch Reg.partnerLeft Reg.partnerRight

def pair1 (d : Data) := d.set Reg.value (d.1 Reg.right)
def pair2 (d : Data) := (pair1 d).set Reg.value (d.1 Reg.right+d.1 Reg.one)
def pair3 (d : Data) := writeState (pair2 d) Reg.partnerLeft Reg.left Reg.value
def pair4 (d : Data) := (pair3 d).set Reg.value (d.1 Reg.left)
def pair5 (d : Data) := (pair4 d).set Reg.value (d.1 Reg.left+d.1 Reg.one)
def pairState (d : Data) := writeState (pair5 d) Reg.partnerRight Reg.right Reg.value

attribute [local simp] pair1 pair2 pair3 pair4 pair5 pairState writeState NaturalData.set NaturalData.store

theorem pair_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (l : Fin input.1) (r : Fin input.2.1) (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) :
    Natural.Exec B pair d (pairState d) 8 ∧
      Representation input (BipartiteMatching.pair matching l r) paths (pairState d) ∧
      NaturalData.Bounded B (pairState d) := by
  have nBound : input.1≤B := by
    have bound : input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  have mBound : input.2.1≤B := by
    have bound : input.2.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  have leftPtr := rep.pointers Slot.partnerLeft
  have rightPtr := rep.pointers Slot.partnerRight
  change d.1 Reg.partnerLeft=(Layout.ofInput input).base Slot.partnerLeft at leftPtr
  change d.1 Reg.partnerRight=(Layout.ofInput input).base Slot.partnerRight at rightPtr
  have first : Natural.Exec B (copy Reg.value Reg.right) d (pair1 d) 1 := Natural.Exec.atom (Natural.Step.copy d Reg.value Reg.right (before.1 _))
  have second : Natural.Exec B (increment Reg.value) (pair1 d) (pair2 d) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (pair1 d) Reg.value Reg.value Reg.one
      (by simp [right,rep.one]; exact (show r.val+1≤ input.2.1 by have := r.isLt; omega).trans mBound))
  have third : Natural.Exec B (write Reg.partnerLeft Reg.left Reg.value) (pair2 d) (pair3 d) 2 := native_write _ _ _ _ (by decide)
    (by simpa [left,leftPtr] using ((Layout.ofInput input).address_bound Slot.partnerLeft l.val l.isLt).le.trans room)
    (by simp [right,rep.one]; exact (show r.val+1≤ input.2.1 by have := r.isLt; omega).trans mBound)
  have fourth : Natural.Exec B (copy Reg.value Reg.left) (pair3 d) (pair4 d) 1 :=
    Natural.Exec.atom (Natural.Step.copy (pair3 d) Reg.value Reg.left (by simpa using before.1 Reg.left))
  have fifth : Natural.Exec B (increment Reg.value) (pair4 d) (pair5 d) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (pair4 d) Reg.value Reg.value Reg.one
      (by simp [left,rep.one]; exact (show l.val+1≤ input.1 by have := l.isLt; omega).trans nBound))
  have sixth : Natural.Exec B (write Reg.partnerRight Reg.right Reg.value) (pair5 d) (pairState d) 2 := native_write _ _ _ _ (by decide)
    (by simpa [right,rightPtr] using ((Layout.ofInput input).address_bound Slot.partnerRight r.val r.isLt).le.trans room)
    (by simp [left,rep.one]; exact (show l.val+1≤ input.1 by have := l.isLt; omega).trans nBound)
  have trace : Natural.Exec B pair d (pairState d) 8 := first.seq (second.seq (third.seq (fourth.seq (fifth.seq sixth))))
  have memory : (pairState d).2=pairMemory input d.2 l r := by simp [pairMemory,leftPtr,rightPtr,left,right,rep.one]
  have represented : MemoryRep input (BipartiteMatching.pair matching l r) paths (pairState d).2 := by
    rw [memory]
    exact pairMemory_represents input matching paths d.2 rep.memory pathsBound l r
  have frame : PreservesLayout pair := by
    constructor
    · intro slot; fin_cases slot <;> decide
    · decide
  exact ⟨trace,rep.of_execution input matching (BipartiteMatching.pair matching l r) paths paths d _ trace frame represented,trace.bounded before⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
