/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMReached

/-! # One original edge record implements one logical discovery step -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.index Reg.left Reg.right Reg.length Reg.value Reg.scratch

theorem scanBody_simulates {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (i : Fin input.2.2.length) (index : d.1 Reg.index=i.val) :
    ∃ result cost, Natural.Exec B scanBody d result cost ∧ cost≤40*(input.1+1) ∧
      Representation input matching (DenseSearch.discover matching paths (input.2.2.get i)) result ∧
      NaturalData.Bounded B result ∧ result.1 Reg.index=i.val+1 := by
  let edge := input.2.2.get i
  obtain ⟨first,rep1,bound1⟩ := read_slot input matching paths d rep before room Slot.edgeLeft i.val i.isLt Reg.index Reg.left index (by decide)
  let d1 := readState d Reg.edgeLeft Reg.index Reg.left
  change Natural.Exec B (read Reg.edgeLeft Reg.index Reg.left) d d1 2 at first
  change Representation input matching paths d1 at rep1
  change NaturalData.Bounded B d1 at bound1
  have left1 : d1.1 Reg.left=edge.1.val :=
    (read_slot_value input matching paths d rep Slot.edgeLeft i.val Reg.index Reg.left index).trans (rep.memory.edgeLeft i)
  have index1 : d1.1 Reg.index=i.val := by simp [d1,readState,NaturalData.set,index]
  obtain ⟨second,rep2,bound2⟩ := read_slot input matching paths d1 rep1 bound1 room Slot.edgeRight i.val i.isLt Reg.index Reg.right index1 (by decide)
  let d2 := readState d1 Reg.edgeRight Reg.index Reg.right
  change Natural.Exec B (read Reg.edgeRight Reg.index Reg.right) d1 d2 2 at second
  change Representation input matching paths d2 at rep2
  change NaturalData.Bounded B d2 at bound2
  have right2 : d2.1 Reg.right=edge.2.val :=
    (read_slot_value input matching paths d1 rep1 Slot.edgeRight i.val Reg.index Reg.right index1).trans (rep1.memory.edgeRight i)
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
  have action : ∃ result cost,
      Natural.Exec B (.branch (.eq Reg.length Reg.zero) skip discoverReached) d3 result cost ∧ cost≤24*(input.1+1)+2 ∧
      Representation input matching (DenseSearch.discover matching paths edge) result ∧ NaturalData.Bounded B result := by
    cases marked : paths edge.1 with
    | none =>
      have condition : Natural.Holds (.eq Reg.length Reg.zero) d3 := by simp only [Natural.Holds,length3,marked,lengthCode,rep3.zero]
      refine ⟨d3,2,Natural.Exec.branch_yes condition (native_skip d3 bound3),by omega,?_,bound3⟩
      simpa only [DenseSearch.discover,marked] using rep3
    | some prior =>
      have condition : ¬Natural.Holds (.eq Reg.length Reg.zero) d3 := by
        simp only [Natural.Holds,length3,marked,lengthCode,rep3.zero]
        omega
      obtain ⟨result,cost,execution,budget,represented,bounded⟩ := discoverReached_simulates input matching paths d3 rep3 bound3 room inv
        edge.1 edge.2 prior (List.get_mem ..) marked left3 right3 (by simpa [marked,lengthCode] using length3)
      exact ⟨result,cost+2,Natural.Exec.branch_no condition execution,by omega,represented,bounded⟩
  obtain ⟨middle,cost,body,budget,middleRep,middleBound⟩ := action
  have beforeIncrement := first.seq (second.seq (third.seq body))
  have middleIndex : middle.1 Reg.index=i.val := (beforeIncrement.register_eq (by decide)).trans index
  have edgesBound : input.2.2.length≤B := by
    have bound : input.2.2.length≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let result := middle.set Reg.index (middle.1 Reg.index+middle.1 Reg.one)
  have last : Natural.Exec B (increment Reg.index) middle result 1 :=
    Natural.Exec.atom (Natural.Step.add middle Reg.index Reg.index Reg.one (by rw [middleIndex,middleRep.one]; exact (show i.val+1≤ input.2.2.length by have := i.isLt; omega).trans edgesBound))
  have finalRep := middleRep.set_scalar input matching (DenseSearch.discover matching paths edge) middle Reg.index (middle.1 Reg.index+middle.1 Reg.one)
    (scalarRegister_of_large _ (by decide)) (by decide)
  refine ⟨result,2+(2+(2+(cost+1))),?_,by omega,finalRep,last.bounded middleBound,?_⟩
  · simpa only [scanBody] using first.seq (second.seq (third.seq (body.seq last)))
  · simp [result,NaturalData.set,middleIndex,middleRep.one]

end LeanTrominoes.BipartiteMatching.DenseWordRAM
