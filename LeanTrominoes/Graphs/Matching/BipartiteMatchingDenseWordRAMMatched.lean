/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMFreshSimulation
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRead

/-! # Skipping a known matched neighbor or installing its fresh path -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.n Reg.m Reg.edges Reg.left Reg.right Reg.mate Reg.length Reg.value Reg.scratch

theorem discoverMatched_simulates {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (l target : Fin input.1) (r : Fin input.2.1) (prior : List (Fin input.1 × Fin input.2.1))
    (edge : (l,r)∈input.2.2) (marked : paths l=some prior) (paired : matching.right r=some target)
    (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) (mate : d.1 Reg.mate=target.val+1)
    (length : d.1 Reg.length=prior.length+1) :
    ∃ result cost, Natural.Exec B discoverMatched d result cost ∧ cost≤20*(input.1+1) ∧
      Representation input matching (DenseSearch.discover matching paths (l,r)) result ∧ NaturalData.Bounded B result := by
  let lower := d.set Reg.mate (d.1 Reg.mate-d.1 Reg.one)
  have first : Natural.Exec B (decrement Reg.mate) d lower 1 :=
    Natural.Exec.atom (Natural.Step.sub d Reg.mate Reg.mate Reg.one
      (by rw [mate,rep.one]; omega) ((Nat.sub_le _ _).trans (before.1 Reg.mate)))
  have lowerRep := rep.set_scalar input matching paths d Reg.mate (d.1 Reg.mate-d.1 Reg.one) (scalarRegister_of_large _ (by decide)) (by decide)
  have lowerMate : lower.1 Reg.mate=target.val := by simp [lower,NaturalData.set,mate,rep.one]
  obtain ⟨second,readRep,readBound⟩ := read_slot input matching paths lower lowerRep (first.bounded before) room
    Slot.lengths target.val target.isLt Reg.mate Reg.value lowerMate (by decide)
  let middle := readState lower Reg.lengths Reg.mate Reg.value
  change Natural.Exec B (read Reg.lengths Reg.mate Reg.value) lower middle 2 at second
  change Representation input matching paths middle at readRep
  change NaturalData.Bounded B middle at readBound
  have value : middle.1 Reg.value=lengthCode (paths target) :=
    (read_slot_value input matching paths lower lowerRep Slot.lengths target.val Reg.mate Reg.value lowerMate).trans (rep.memory.lengths target)
  have middleLeft : middle.1 Reg.left=l.val := by simp [middle,lower,readState,NaturalData.set,left]
  have middleRight : middle.1 Reg.right=r.val := by simp [middle,lower,readState,NaturalData.set,right]
  have middleMate : middle.1 Reg.mate=target.val := by simp [middle,readState,NaturalData.set,lowerMate]
  have middleLength : middle.1 Reg.length=prior.length+1 := by simp [middle,lower,readState,NaturalData.set,length]
  cases found : paths target with
  | none =>
    have condition : Natural.Holds (.eq Reg.value Reg.zero) middle := by
      simp only [Natural.Holds,value,found,lengthCode,readRep.zero]
    obtain ⟨cost,third,budget,finalRep,finalBound⟩ := fresh_simulates input matching paths middle readRep readBound room inv
      l target r prior edge marked found paired middleLeft middleRight middleMate middleLength
    have branch := Natural.Exec.branch_yes (no := skip) condition third
    have trace := first.seq (second.seq branch)
    have countBound := path_length_bound inv l prior marked
    simp only [Fintype.card_fin] at countBound
    exact ⟨freshState middle,1+(2+(cost+1)),by simpa only [discoverMatched] using trace,by omega,finalRep,finalBound⟩
  | some old =>
    have condition : ¬Natural.Holds (.eq Reg.value Reg.zero) middle := by
      simp only [Natural.Holds,value,found,lengthCode,readRep.zero]
      omega
    have branch := Natural.Exec.branch_no (yes := discoverFresh) condition (native_skip middle readBound)
    have trace := first.seq (second.seq branch)
    refine ⟨middle,6,?_,by omega,?_,readBound⟩
    · simpa only [discoverMatched,Nat.reduceAdd] using trace
    · simpa only [DenseSearch.discover,marked,paired,found,Option.isNone_some,Bool.false_eq_true,ite_false] using readRep

end LeanTrominoes.BipartiteMatching.DenseWordRAM
