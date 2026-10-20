/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMAugmentLoop
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMTerminalRecord

/-! # Complete path rewriting by the fixed bounded-word RAM program -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.n Reg.left Reg.right Reg.length Reg.source Reg.copyIndex Reg.foundLeft Reg.foundRight

theorem writePairs_append (matching : State (Fin n) (Fin m)) (a b : List (Fin n × Fin m)) :
    DenseSearch.writePairs matching (a++b)=DenseSearch.writePairs (DenseSearch.writePairs matching a) b := by
  induction a generalizing matching with
  | nil => rfl
  | cons edge rest ih => cases edge; simpa only [List.cons_append,DenseSearch.writePairs] using ih (BipartiteMatching.pair matching _ _)

theorem augment_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (l : Fin input.1) (r : Fin input.2.1) (prior : List (Fin input.1 × Fin input.2.1))
    (marked : paths l=some prior) (selected : Selected input (some (l,r)) d) :
    ∃ result cost, Natural.Exec B augment d result cost ∧ cost≤20*(input.1+1) ∧
      Representation input (DenseSearch.writePairs matching (prior++[(l,r)])) paths result ∧ NaturalData.Bounded B result := by
  have foundLeft := selected.1
  have foundRight := selected.2
  have cellsBound : input.1*input.1≤B := by
    have bound : input.1*input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let d1 := d.set Reg.source (d.1 Reg.foundLeft*d.1 Reg.n)
  have first : Natural.Exec B (mul Reg.source Reg.foundLeft Reg.n) d d1 1 :=
    Natural.Exec.atom (Natural.Step.mul d Reg.source Reg.foundLeft Reg.n
      (by rw [foundLeft,rep.n]; exact (Nat.mul_le_mul_right input.1 l.isLt.le).trans cellsBound))
  have rep1 := rep.set_scalar input matching paths d Reg.source (d.1 Reg.foundLeft*d.1 Reg.n) (scalarRegister_of_large _ (by decide)) (by decide)
  have foundLeft1 : d1.1 Reg.foundLeft=l.val := by simp [d1,NaturalData.set,foundLeft]
  obtain ⟨second,rep2,bound2⟩ := read_slot input matching paths d1 rep1 (first.bounded before) room Slot.lengths l.val l.isLt Reg.foundLeft Reg.length foundLeft1 (by decide)
  let d2 := readState d1 Reg.lengths Reg.foundLeft Reg.length
  change Natural.Exec B (read Reg.lengths Reg.foundLeft Reg.length) d1 d2 2 at second
  change Representation input matching paths d2 at rep2
  change NaturalData.Bounded B d2 at bound2
  have length2 : d2.1 Reg.length=prior.length+1 := by
    have value := (read_slot_value input matching paths d1 rep1 Slot.lengths l.val Reg.foundLeft Reg.length foundLeft1).trans (rep1.memory.lengths l)
    change d2.1 Reg.length=lengthCode (paths l) at value
    simpa only [marked,lengthCode] using value
  let d3 := d2.set Reg.length (d2.1 Reg.length-d2.1 Reg.one)
  have third : Natural.Exec B (decrement Reg.length) d2 d3 1 :=
    Natural.Exec.atom (Natural.Step.sub d2 Reg.length Reg.length Reg.one
      (by rw [length2,rep2.one]; omega) ((Nat.sub_le _ _).trans (bound2.1 _)))
  have rep3 := rep2.set_scalar input matching paths d2 Reg.length (d2.1 Reg.length-d2.1 Reg.one) (scalarRegister_of_large _ (by decide)) (by decide)
  let d4 := d3.set Reg.copyIndex 0
  have fourth : Natural.Exec B (constant Reg.copyIndex 0) d3 d4 1 := Natural.Exec.atom (Natural.Step.constant d3 Reg.copyIndex 0 (Nat.zero_le B))
  have rep4 := rep3.set_scalar input matching paths d3 Reg.copyIndex 0 (scalarRegister_of_large _ (by decide)) (by decide)
  have source4 : d4.1 Reg.source=l.val*input.1 := by simp [d4,d3,d2,d1,readState,NaturalData.set,foundLeft,rep.n,Reg.scratch]
  have length4 : d4.1 Reg.length=prior.length := by simp [d4,d3,NaturalData.set,length2,rep2.one]
  obtain ⟨middle,loopCost,loopRun,loopBudget,middleRep,middleBound⟩ := augmentLoop_exec input prior.length matching paths d4 rep4 pathsBound
    ((third.seq fourth).bounded bound2) room l prior marked source4 length4 (by simp [d4,NaturalData.set])
  have middleRep' : Representation input (DenseSearch.writePairs matching prior) paths middle := by
    simpa only [d4,NaturalData.set,Function.update_self,List.drop_zero] using middleRep
  have initial := first.seq (second.seq (third.seq (fourth.seq loopRun)))
  have middleLeft : middle.1 Reg.foundLeft=l.val := (initial.register_eq (by decide)).trans foundLeft
  have middleRight : middle.1 Reg.foundRight=r.val+1 := (initial.register_eq (by decide)).trans foundRight
  let d5 := middle.set Reg.left (middle.1 Reg.foundLeft)
  have copyLeft : Natural.Exec B (copy Reg.left Reg.foundLeft) middle d5 1 :=
    Natural.Exec.atom (Natural.Step.copy middle Reg.left Reg.foundLeft (middleBound.1 _))
  have rep5 := middleRep'.set_scalar input _ paths middle Reg.left (middle.1 Reg.foundLeft) (scalarRegister_of_large _ (by decide)) (by decide)
  let d6 := d5.set Reg.right (d5.1 Reg.foundRight)
  have copyRight : Natural.Exec B (copy Reg.right Reg.foundRight) d5 d6 1 :=
    Natural.Exec.atom (Natural.Step.copy d5 Reg.right Reg.foundRight (by simpa [d5,NaturalData.set] using middleBound.1 Reg.foundRight))
  have rep6 := rep5.set_scalar input _ paths d5 Reg.right (d5.1 Reg.foundRight) (scalarRegister_of_large _ (by decide)) (by decide)
  have right6 : d6.1 Reg.right=r.val+1 := by simp [d6,d5,NaturalData.set,middleRight]
  let d7 := d6.set Reg.right (d6.1 Reg.right-d6.1 Reg.one)
  have lowerRight : Natural.Exec B (decrement Reg.right) d6 d7 1 :=
    Natural.Exec.atom (Natural.Step.sub d6 Reg.right Reg.right Reg.one
      (by rw [right6,rep6.one]; omega) ((Nat.sub_le _ _).trans (((copyLeft.seq copyRight).bounded middleBound).1 Reg.right)))
  have rep7 := rep6.set_scalar input _ paths d6 Reg.right (d6.1 Reg.right-d6.1 Reg.one) (scalarRegister_of_large _ (by decide)) (by decide)
  have left7 : d7.1 Reg.left=l.val := by simp [d7,d6,d5,NaturalData.set,middleLeft]
  have right7 : d7.1 Reg.right=r.val := by
    change d6.1 Reg.right-d6.1 Reg.one=r.val
    rw [right6,rep6.one]
    omega
  obtain ⟨paired,finalRep,finalBound⟩ := pair_exec input _ paths d7 rep7 pathsBound
    ((copyLeft.seq (copyRight.seq lowerRight)).bounded middleBound) room l r left7 right7
  have trace := first.seq (second.seq (third.seq (fourth.seq (loopRun.seq (copyLeft.seq (copyRight.seq (lowerRight.seq paired)))))))
  refine ⟨pairState d7,loopCost+16,?_,?_,?_,finalBound⟩
  · simpa only [augment,Nat.reduceAdd,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using trace
  · have pathLength := pathsBound l prior marked
    omega
  · simpa only [writePairs_append,DenseSearch.writePairs] using finalRep

end LeanTrominoes.BipartiteMatching.DenseWordRAM
