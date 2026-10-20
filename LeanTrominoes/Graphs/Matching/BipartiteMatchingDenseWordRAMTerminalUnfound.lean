/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMTerminalRecord

/-! # Testing one original edge before a terminal has been found -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.index Reg.left Reg.right Reg.length Reg.mate Reg.value Reg.scratch Reg.foundRight

def terminalTest (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (edge : Fin input.1 × Fin input.2.1) : Bool :=
  (paths edge.1).isSome && (matching.right edge.2).isNone

theorem terminalUnfound_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B) (i : Fin input.2.2.length)
    (index : d.1 Reg.index=i.val) (selected : Selected input none d) :
    ∃ result cost, Natural.Exec B terminalUnfound d result cost ∧ cost≤14 ∧
      Representation input matching paths result ∧ NaturalData.Bounded B result ∧
      Selected input (if terminalTest input matching paths (input.2.2.get i) then some (input.2.2.get i) else none) result := by
  let edge := input.2.2.get i
  obtain ⟨first,rep1,bound1⟩ := read_slot input matching paths d rep before room Slot.edgeLeft i.val i.isLt Reg.index Reg.left index (by decide)
  let d1 := readState d Reg.edgeLeft Reg.index Reg.left
  change Natural.Exec B (read Reg.edgeLeft Reg.index Reg.left) d d1 2 at first
  change Representation input matching paths d1 at rep1
  change NaturalData.Bounded B d1 at bound1
  have left1 : d1.1 Reg.left=edge.1.val := (read_slot_value input matching paths d rep Slot.edgeLeft i.val Reg.index Reg.left index).trans (rep.memory.edgeLeft i)
  obtain ⟨second,rep2,bound2⟩ := read_slot input matching paths d1 rep1 bound1 room Slot.edgeRight i.val i.isLt Reg.index Reg.right
    (by simp [d1,readState,NaturalData.set,index]) (by decide)
  let d2 := readState d1 Reg.edgeRight Reg.index Reg.right
  change Natural.Exec B (read Reg.edgeRight Reg.index Reg.right) d1 d2 2 at second
  change Representation input matching paths d2 at rep2
  change NaturalData.Bounded B d2 at bound2
  have right2 : d2.1 Reg.right=edge.2.val :=
    (read_slot_value input matching paths d1 rep1 Slot.edgeRight i.val Reg.index Reg.right (by simp [d1,readState,NaturalData.set,index])).trans (rep1.memory.edgeRight i)
  have left2 : d2.1 Reg.left=edge.1.val := by simp [d2,readState,NaturalData.set,left1]
  obtain ⟨third,rep3,bound3⟩ := read_slot input matching paths d2 rep2 bound2 room Slot.lengths edge.1.val edge.1.isLt Reg.left Reg.length left2 (by decide)
  let d3 := readState d2 Reg.lengths Reg.left Reg.length
  change Natural.Exec B (read Reg.lengths Reg.left Reg.length) d2 d3 2 at third
  change Representation input matching paths d3 at rep3
  change NaturalData.Bounded B d3 at bound3
  have length3 : d3.1 Reg.length=lengthCode (paths edge.1) :=
    (read_slot_value input matching paths d2 rep2 Slot.lengths edge.1.val Reg.left Reg.length left2).trans (rep2.memory.lengths edge.1)
  have left3 : d3.1 Reg.left=edge.1.val := by simp [d3,readState,NaturalData.set,left2]
  have right3 : d3.1 Reg.right=edge.2.val := by simp [d3,readState,NaturalData.set,right2]
  have selected3 : Selected input none d3 := by simpa [Selected,d3,d2,d1,readState,NaturalData.set] using selected
  cases marked : paths edge.1 with
  | none =>
    have condition : Natural.Holds (.eq Reg.length Reg.zero) d3 := by simp only [Natural.Holds,length3,marked,lengthCode,rep3.zero]
    have branch := Natural.Exec.branch_yes (no := terminalReached) condition (native_skip d3 bound3)
    refine ⟨d3,8,?_,by omega,rep3,bound3,?_⟩
    · simpa only [terminalUnfound,Nat.reduceAdd] using first.seq (second.seq (third.seq branch))
    · change Selected input (if terminalTest input matching paths edge then some edge else none) d3
      simpa only [terminalTest,marked,Option.isSome_none,Bool.false_and,Bool.false_eq_true,ite_false] using selected3
  | some prior =>
    have condition : ¬Natural.Holds (.eq Reg.length Reg.zero) d3 := by
      simp only [Natural.Holds,length3,marked,lengthCode,rep3.zero]
      omega
    obtain ⟨fourth,rep4,bound4⟩ := read_slot input matching paths d3 rep3 bound3 room Slot.partnerRight edge.2.val edge.2.isLt Reg.right Reg.mate right3 (by decide)
    let d4 := readState d3 Reg.partnerRight Reg.right Reg.mate
    change Natural.Exec B (read Reg.partnerRight Reg.right Reg.mate) d3 d4 2 at fourth
    change Representation input matching paths d4 at rep4
    change NaturalData.Bounded B d4 at bound4
    have mate4 : d4.1 Reg.mate=optionCode (matching.right edge.2) :=
      (read_slot_value input matching paths d3 rep3 Slot.partnerRight edge.2.val Reg.right Reg.mate right3).trans (rep3.memory.partnerRight edge.2)
    have selected4 : Selected input none d4 := by simpa [Selected,d4,readState,NaturalData.set] using selected3
    cases paired : matching.right edge.2 with
    | none =>
      have free : Natural.Holds (.eq Reg.mate Reg.zero) d4 := by simp only [Natural.Holds,mate4,paired,optionCode,rep4.zero]
      obtain ⟨recorded,finalRep,finalBound,finalSelected⟩ := recordTerminal_exec input matching paths d4 rep4 bound4 room edge.1 edge.2
        (by simp [d4,readState,NaturalData.set,left3]) (by simp [d4,readState,NaturalData.set,right3])
      have hit := Natural.Exec.branch_yes (no := skip) free recorded
      have branch := Natural.Exec.branch_no (yes := skip) condition (fourth.seq hit)
      refine ⟨recordState d4,14,?_,by omega,finalRep,finalBound,?_⟩
      · simpa only [terminalUnfound,terminalReached,Nat.reduceAdd] using first.seq (second.seq (third.seq branch))
      · change Selected input (if terminalTest input matching paths edge then some edge else none) (recordState d4)
        simpa only [terminalTest,marked,paired,Option.isSome_some,Option.isNone_none,Bool.true_and,ite_true] using finalSelected
    | some target =>
      have matched : ¬Natural.Holds (.eq Reg.mate Reg.zero) d4 := by simp only [Natural.Holds,mate4,paired,optionCode,rep4.zero]; omega
      have miss := Natural.Exec.branch_no (yes := recordTerminal) matched (native_skip d4 bound4)
      have branch := Natural.Exec.branch_no (yes := skip) condition (fourth.seq miss)
      refine ⟨d4,13,?_,by omega,rep4,bound4,?_⟩
      · simpa only [terminalUnfound,terminalReached,Nat.reduceAdd] using first.seq (second.seq (third.seq branch))
      · change Selected input (if terminalTest input matching paths edge then some edge else none) d4
        simpa only [terminalTest,marked,paired,Option.isSome_some,Option.isNone_some,Bool.true_and,Bool.false_eq_true,ite_false] using selected4

end LeanTrominoes.BipartiteMatching.DenseWordRAM
