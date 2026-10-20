/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMCopyLoop
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRepresentation

/-! # Primitive execution of a fresh alternating-prefix discovery -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.n Reg.m Reg.edges Reg.left Reg.right Reg.mate Reg.length
  Reg.source Reg.target Reg.copyIndex Reg.rowIndex Reg.rowLeft Reg.rowRight Reg.lengths Reg.value Reg.scratch

def fresh1 (d : Data) := d.set Reg.source (d.1 Reg.left*d.1 Reg.n)
def fresh2 (d : Data) := (fresh1 d).set Reg.target (d.1 Reg.mate*d.1 Reg.n)
def fresh3 (d : Data) := (fresh2 d).set Reg.copyIndex 0
def fresh4 (d : Data) := (fresh3 d).set Reg.length (d.1 Reg.length-d.1 Reg.one)
def fresh5 (d : Data) := copyState^[(fresh4 d).1 Reg.length] (fresh4 d)
def fresh6 (d : Data) := (fresh5 d).set Reg.rowIndex ((fresh5 d).1 Reg.target+(fresh5 d).1 Reg.length)
def fresh7 (d : Data) := writeState (fresh6 d) Reg.rowLeft Reg.rowIndex Reg.left
def fresh8 (d : Data) := writeState (fresh7 d) Reg.rowRight Reg.rowIndex Reg.right
def fresh9 (d : Data) := (fresh8 d).set Reg.length ((fresh8 d).1 Reg.length+(fresh8 d).1 Reg.one)
def fresh10 (d : Data) := (fresh9 d).set Reg.length ((fresh9 d).1 Reg.length+(fresh9 d).1 Reg.one)
def freshState (d : Data) := writeState (fresh10 d) Reg.lengths Reg.mate Reg.length

attribute [local simp] fresh1 fresh2 fresh3 fresh4 fresh6 fresh7 fresh8 fresh9 fresh10
  readState writeState NaturalData.set NaturalData.store

theorem fresh4_fixed (d : Data) (i : Fin 64)
    (different : i≠Reg.source ∧ i≠Reg.target ∧ i≠Reg.copyIndex ∧ i≠Reg.length) : (fresh4 d).1 i=d.1 i := by simp_all

theorem fresh5_fixed (d : Data) (i : Fin 64)
    (different : i≠Reg.source ∧ i≠Reg.target ∧ i≠Reg.copyIndex ∧ i≠Reg.length ∧
      i≠Reg.rowIndex ∧ i≠Reg.value ∧ i≠Reg.scratch) : (fresh5 d).1 i=d.1 i := by
  rw [fresh5,copy_iterate_fixed _ _ i ⟨different.2.2.1,different.2.2.2.2.1,different.2.2.2.2.2.1,different.2.2.2.2.2.2⟩]
  exact fresh4_fixed d i ⟨different.1,different.2.1,different.2.2.1,different.2.2.2.1⟩

theorem fresh5_source (d : Data) : (fresh5 d).1 Reg.source=d.1 Reg.left*d.1 Reg.n := by
  rw [fresh5,copy_iterate_fixed _ _ Reg.source (by decide)]
  simp

theorem fresh5_target (d : Data) : (fresh5 d).1 Reg.target=d.1 Reg.mate*d.1 Reg.n := by
  rw [fresh5,copy_iterate_fixed _ _ Reg.target (by decide)]
  simp

theorem fresh5_length (d : Data) : (fresh5 d).1 Reg.length=d.1 Reg.length-d.1 Reg.one := by
  rw [fresh5,copy_iterate_fixed _ _ Reg.length (by decide)]
  simp

attribute [local simp] fresh5_fixed fresh5_source fresh5_target fresh5_length

theorem fresh_exec {B count : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B) (l target : Fin input.1) (r : Fin input.2.1)
    (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) (mate : d.1 Reg.mate=target.val)
    (length : d.1 Reg.length=count+1) (lengthBound : count+2≤ input.1) :
    ∃ cost, Natural.Exec B discoverFresh d (freshState d) cost ∧ cost≤15*count+15 := by
  let a := Layout.ofInput input
  have nBound : input.1≤B := by
    have bound : input.1≤a.frontier := by dsimp [a,Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  have mBound : input.2.1≤B := by
    have bound : input.2.1≤a.frontier := by dsimp [a,Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  have cellsBound : input.1*input.1≤B := by
    have bound : input.1*input.1≤a.frontier := by dsimp [a,Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  have sourceEnd : l.val*input.1+count≤ input.1*input.1 := by have := l.isLt; nlinarith
  have targetEnd : target.val*input.1+count≤ input.1*input.1 := by have := target.isLt; nlinarith
  have leftPtr := rep.pointers Slot.rowLeft
  have rightPtr := rep.pointers Slot.rowRight
  have lengthPtr := rep.pointers Slot.lengths
  change d.1 Reg.rowLeft=a.base Slot.rowLeft at leftPtr
  change d.1 Reg.rowRight=a.base Slot.rowRight at rightPtr
  change d.1 Reg.lengths=a.base Slot.lengths at lengthPtr
  have first : Natural.Exec B (mul Reg.source Reg.left Reg.n) d (fresh1 d) 1 := by
    exact Natural.Exec.atom (Natural.Step.mul d Reg.source Reg.left Reg.n (by rw [left,rep.n]; exact (Nat.le_add_right _ _).trans (sourceEnd.trans cellsBound)))
  have second : Natural.Exec B (mul Reg.target Reg.mate Reg.n) (fresh1 d) (fresh2 d) 1 := by
    simpa [mul] using Natural.Exec.atom (Natural.Step.mul (bound := B) (fresh1 d) Reg.target Reg.mate Reg.n (by simp [mate,rep.n]; exact (Nat.le_add_right _ _).trans (targetEnd.trans cellsBound)))
  have third : Natural.Exec B (constant Reg.copyIndex 0) (fresh2 d) (fresh3 d) 1 := Natural.Exec.atom (Natural.Step.constant _ _ _ (Nat.zero_le B))
  have fourth : Natural.Exec B (decrement Reg.length) (fresh3 d) (fresh4 d) 1 := by
    simpa [decrement,sub] using Natural.Exec.atom (Natural.Step.sub (bound := B) (fresh3 d) Reg.length Reg.length Reg.one
      (by simp [length,rep.one]) (by simp [length,rep.one]; omega))
  have initial := first.seq (second.seq (third.seq fourth))
  have copyRoom : CopyRoom B count (fresh4 d) := by
    simp only [CopyRoom,fresh4,fresh3,fresh2,fresh1,NaturalData.set]
    simp only [Reg.copyIndex,Reg.length,Reg.source,Reg.target,Reg.left,Reg.n,Reg.mate,Reg.one,Reg.rowLeft,Reg.rowRight,Function.update_self,Function.update_of_ne (by decide : (14 : Fin 64)≠23),Function.update_of_ne (by decide : (15 : Fin 64)≠23)]
    simp [left,mate,rep.n,length,rep.one,leftPtr,rightPtr]
    simp [a,Layout.ofInput,Layout.base,Layout.frontier,Slot.rowLeft,Slot.rowRight] at room ⊢
    omega
  obtain ⟨copyCost,copied,copyBudget⟩ := copyLoop_exec (fresh4 d) copyRoom
    (by simp [rep.one]) (by simp) (by simp [length,rep.one]) (initial.bounded before)
  have copied' : Natural.Exec B (.loop (.lt Reg.copyIndex Reg.length) copyPair) (fresh4 d) (fresh5 d) copyCost := by
    simpa [fresh5,length,rep.one] using copied
  have offsetBound : target.val*input.1+count<a.length Slot.rowLeft := row_index_bound target.isLt (by omega)
  have addIndex : Natural.Exec B (add Reg.rowIndex Reg.target Reg.length) (fresh5 d) (fresh6 d) 1 := by
    exact Natural.Exec.atom (Natural.Step.add (fresh5 d) Reg.rowIndex Reg.target Reg.length
      (by simp [mate,rep.n,length,rep.one]; exact targetEnd.trans cellsBound))
  have writeLeft : Natural.Exec B (write Reg.rowLeft Reg.rowIndex Reg.left) (fresh6 d) (fresh7 d) 2 :=
    native_write _ _ _ _ (by decide)
      (by simpa [mate,rep.n,length,rep.one,leftPtr] using (a.address_bound Slot.rowLeft _ offsetBound).le.trans room)
      (by simpa [left] using l.isLt.le.trans nBound)
  have writeRight : Natural.Exec B (write Reg.rowRight Reg.rowIndex Reg.right) (fresh7 d) (fresh8 d) 2 :=
    native_write _ _ _ _ (by decide)
      (by simpa [mate,rep.n,length,rep.one,rightPtr] using (a.address_bound Slot.rowRight _ offsetBound).le.trans room)
      (by simpa [right] using r.isLt.le.trans mBound)
  have incrementOne : Natural.Exec B (increment Reg.length) (fresh8 d) (fresh9 d) 1 :=
    Natural.Exec.atom (Natural.Step.add (fresh8 d) Reg.length Reg.length Reg.one (by simp [length,rep.one]; omega))
  have incrementTwo : Natural.Exec B (increment Reg.length) (fresh9 d) (fresh10 d) 1 :=
    Natural.Exec.atom (Natural.Step.add (fresh9 d) Reg.length Reg.length Reg.one (by simp [length,rep.one]; omega))
  have storeLength : Natural.Exec B (write Reg.lengths Reg.mate Reg.length) (fresh10 d) (freshState d) 2 :=
    native_write _ _ _ _ (by decide)
      (by simpa [mate,lengthPtr] using (a.address_bound Slot.lengths target.val target.isLt).le.trans room)
      (by simp [length,rep.one]; omega)
  have trace := first.seq (second.seq (third.seq (fourth.seq
    (copied'.seq (addIndex.seq (writeLeft.seq (writeRight.seq (incrementOne.seq (incrementTwo.seq storeLength)))))))))
  refine ⟨1+(1+(1+(1+(copyCost+(1+(2+(2+(1+(1+2))))))))),?_,by omega⟩
  simpa only [discoverFresh] using trace

end LeanTrominoes.BipartiteMatching.DenseWordRAM
