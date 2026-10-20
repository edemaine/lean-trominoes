/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMMatched

/-! # Following an input edge from a reached left vertex -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.left Reg.right Reg.mate Reg.length Reg.value Reg.scratch

theorem discoverReached_simulates {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (l : Fin input.1) (r : Fin input.2.1) (prior : List (Fin input.1 × Fin input.2.1))
    (edge : (l,r)∈input.2.2) (marked : paths l=some prior)
    (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val)
    (length : d.1 Reg.length=prior.length+1) :
    ∃ result cost, Natural.Exec B discoverReached d result cost ∧ cost≤24*(input.1+1) ∧
      Representation input matching (DenseSearch.discover matching paths (l,r)) result ∧ NaturalData.Bounded B result := by
  obtain ⟨first,middleRep,middleBound⟩ := read_slot input matching paths d rep before room
    Slot.partnerRight r.val r.isLt Reg.right Reg.mate right (by decide)
  let middle := readState d Reg.partnerRight Reg.right Reg.mate
  change Natural.Exec B (read Reg.partnerRight Reg.right Reg.mate) d middle 2 at first
  change Representation input matching paths middle at middleRep
  change NaturalData.Bounded B middle at middleBound
  have value : middle.1 Reg.mate=optionCode (matching.right r) :=
    (read_slot_value input matching paths d rep Slot.partnerRight r.val Reg.right Reg.mate right).trans (rep.memory.partnerRight r)
  have middleLeft : middle.1 Reg.left=l.val := by simp [middle,readState,NaturalData.set,left]
  have middleRight : middle.1 Reg.right=r.val := by simp [middle,readState,NaturalData.set,right]
  have middleLength : middle.1 Reg.length=prior.length+1 := by simp [middle,readState,NaturalData.set,length]
  cases paired : matching.right r with
  | none =>
    have condition : Natural.Holds (.eq Reg.mate Reg.zero) middle := by
      simp only [Natural.Holds,value,paired,optionCode,middleRep.zero]
    have branch := Natural.Exec.branch_yes (no := discoverMatched) condition (native_skip middle middleBound)
    refine ⟨middle,4,?_,by omega,?_,middleBound⟩
    · simpa only [discoverReached,Nat.reduceAdd] using first.seq branch
    · simpa only [DenseSearch.discover,marked,paired] using middleRep
  | some target =>
    have condition : ¬Natural.Holds (.eq Reg.mate Reg.zero) middle := by
      simp only [Natural.Holds,value,paired,optionCode,middleRep.zero]
      omega
    obtain ⟨result,cost,second,budget,finalRep,finalBound⟩ := discoverMatched_simulates input matching paths middle middleRep middleBound room inv
      l target r prior edge marked paired middleLeft middleRight (by simpa [paired,optionCode] using value) middleLength
    have branch := Natural.Exec.branch_no (yes := skip) condition second
    exact ⟨result,2+(cost+2),by simpa only [discoverReached] using first.seq branch,by omega,finalRep,finalBound⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
