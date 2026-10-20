/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPair
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRead

/-! # One stored path pair is read and written by fourteen instructions -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.left Reg.right Reg.copyIndex Reg.rowIndex Reg.value Reg.scratch

theorem augmentPair_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (l : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1)) (marked : paths l=some prior)
    (j : Fin prior.length) (source : d.1 Reg.source=l.val*input.1) (index : d.1 Reg.copyIndex=j.val) :
    ∃ result, Natural.Exec B augmentPair d result 14 ∧
      Representation input (BipartiteMatching.pair matching (prior.get j).1 (prior.get j).2) paths result ∧
      NaturalData.Bounded B result ∧ result.1 Reg.copyIndex=j.val+1 := by
  have jbound : j.val< input.1 := j.isLt.trans_le (pathsBound l prior marked)
  have within : l.val*input.1+j.val<(Layout.ofInput input).length Slot.rowLeft := row_index_bound l.isLt jbound
  have cellsBound : input.1*input.1≤B := by
    have bound : input.1*input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let d1 := d.set Reg.rowIndex (d.1 Reg.source+d.1 Reg.copyIndex)
  have first : Natural.Exec B (add Reg.rowIndex Reg.source Reg.copyIndex) d d1 1 :=
    Natural.Exec.atom (Natural.Step.add d Reg.rowIndex Reg.source Reg.copyIndex
      (by rw [source,index]; exact (row_index_bound l.isLt jbound).le.trans cellsBound))
  have rep1 := rep.set_scalar input matching paths d Reg.rowIndex (d.1 Reg.source+d.1 Reg.copyIndex)
    (scalarRegister_of_large _ (by decide)) (by decide)
  have index1 : d1.1 Reg.rowIndex=l.val*input.1+j.val := by simp [d1,NaturalData.set,source,index]
  obtain ⟨second,rep2,bound2⟩ := read_slot input matching paths d1 rep1 (first.bounded before) room Slot.rowLeft _ within Reg.rowIndex Reg.left index1 (by decide)
  let d2 := readState d1 Reg.rowLeft Reg.rowIndex Reg.left
  change Natural.Exec B (read Reg.rowLeft Reg.rowIndex Reg.left) d1 d2 2 at second
  change Representation input matching paths d2 at rep2
  change NaturalData.Bounded B d2 at bound2
  have left2 : d2.1 Reg.left=(prior.get j).1.val :=
    (read_slot_value input matching paths d1 rep1 Slot.rowLeft _ Reg.rowIndex Reg.left index1).trans (rep1.memory.rowLeft l prior marked j)
  have index2 : d2.1 Reg.rowIndex=l.val*input.1+j.val := by simp [d2,readState,NaturalData.set,index1]
  obtain ⟨third,rep3,bound3⟩ := read_slot input matching paths d2 rep2 bound2 room Slot.rowRight _ within Reg.rowIndex Reg.right index2 (by decide)
  let d3 := readState d2 Reg.rowRight Reg.rowIndex Reg.right
  change Natural.Exec B (read Reg.rowRight Reg.rowIndex Reg.right) d2 d3 2 at third
  change Representation input matching paths d3 at rep3
  change NaturalData.Bounded B d3 at bound3
  have right3 : d3.1 Reg.right=(prior.get j).2.val :=
    (read_slot_value input matching paths d2 rep2 Slot.rowRight _ Reg.rowIndex Reg.right index2).trans (rep2.memory.rowRight l prior marked j)
  have left3 : d3.1 Reg.left=(prior.get j).1.val := by simp [d3,readState,NaturalData.set,left2]
  obtain ⟨fourth,rep4,bound4⟩ := pair_exec input matching paths d3 rep3 pathsBound bound3 room (prior.get j).1 (prior.get j).2 left3 right3
  have prefixExecution := first.seq (second.seq (third.seq fourth))
  have copyIndex4 : (pairState d3).1 Reg.copyIndex=j.val := (prefixExecution.register_eq (by decide)).trans index
  have nBound : input.1≤B := by
    have bound : input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let result := (pairState d3).set Reg.copyIndex ((pairState d3).1 Reg.copyIndex+(pairState d3).1 Reg.one)
  have last : Natural.Exec B (increment Reg.copyIndex) (pairState d3) result 1 :=
    Natural.Exec.atom (Natural.Step.add (pairState d3) Reg.copyIndex Reg.copyIndex Reg.one
      (by rw [copyIndex4,rep4.one]; exact (show j.val+1≤ input.1 by omega).trans nBound))
  refine ⟨result,?_,?_,last.bounded bound4,?_⟩
  · simpa only [augmentPair,Nat.reduceAdd] using first.seq (second.seq (third.seq (fourth.seq last)))
  · exact rep4.set_scalar input _ paths (pairState d3) Reg.copyIndex _ (scalarRegister_of_large _ (by decide)) (by decide)
  · simp [result,NaturalData.set,copyIndex4,rep4.one]

end LeanTrominoes.BipartiteMatching.DenseWordRAM
