/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMTerminalUnfound

/-! # One bounded-word terminal-selection scan step -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.zero Reg.index Reg.foundLeft Reg.foundRight

def terminalCandidate (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1))
    (found : Option (Fin input.1 × Fin input.2.1)) (edge : Fin input.1 × Fin input.2.1) :=
  found.orElse (fun _ => if terminalTest input matching paths edge then some edge else none)

theorem selected_set_index (input : Input) (found : Option (Fin input.1 × Fin input.2.1)) (d : Data)
    (selected : Selected input found d) (value : Nat) : Selected input found (d.set Reg.index value) := by
  cases found <;> simpa [Selected,NaturalData.set] using selected

theorem terminalBody_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B) (i : Fin input.2.2.length) (index : d.1 Reg.index=i.val)
    (found : Option (Fin input.1 × Fin input.2.1)) (selected : Selected input found d) :
    ∃ result cost, Natural.Exec B terminalBody d result cost ∧ cost≤16 ∧
      Representation input matching paths result ∧ NaturalData.Bounded B result ∧
      Selected input (terminalCandidate input matching paths found (input.2.2.get i)) result ∧ result.1 Reg.index=i.val+1 := by
  have action : ∃ middle cost,
      Natural.Exec B (.branch (.eq Reg.foundRight Reg.zero) terminalUnfound skip) d middle cost ∧ cost≤15 ∧
      Representation input matching paths middle ∧ NaturalData.Bounded B middle ∧
      Selected input (terminalCandidate input matching paths found (input.2.2.get i)) middle := by
    cases found with
    | none =>
      have condition : Natural.Holds (.eq Reg.foundRight Reg.zero) d := by
        simpa only [Natural.Holds,rep.zero,Selected] using selected
      obtain ⟨result,cost,execution,budget,represented,bounded,chosen⟩ := terminalUnfound_exec input matching paths d rep before room i index selected
      exact ⟨result,cost+1,Natural.Exec.branch_yes condition execution,by omega,represented,bounded,chosen⟩
    | some previous =>
      have condition : ¬Natural.Holds (.eq Reg.foundRight Reg.zero) d := by
        simp only [Natural.Holds,rep.zero,selected.2]
        omega
      exact ⟨d,3,Natural.Exec.branch_no condition (native_skip d before),by omega,rep,before,selected⟩
  obtain ⟨middle,cost,body,budget,middleRep,middleBound,chosen⟩ := action
  have middleIndex : middle.1 Reg.index=i.val := (body.register_eq (by decide)).trans index
  have edgeBound : input.2.2.length≤B := by
    have bound : input.2.2.length≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let result := middle.set Reg.index (middle.1 Reg.index+middle.1 Reg.one)
  have last : Natural.Exec B (increment Reg.index) middle result 1 :=
    Natural.Exec.atom (Natural.Step.add middle Reg.index Reg.index Reg.one
      (by rw [middleIndex,middleRep.one]; exact (show i.val+1≤ input.2.2.length by have := i.isLt; omega).trans edgeBound))
  refine ⟨result,cost+1,body.seq last,by omega,?_,last.bounded middleBound,selected_set_index input _ middle chosen _,?_⟩
  · exact middleRep.set_scalar input matching paths middle Reg.index (middle.1 Reg.index+middle.1 Reg.one)
      (scalarRegister_of_large _ (by decide)) (by decide)
  · simp [result,NaturalData.set,middleIndex,middleRep.one]

end LeanTrominoes.BipartiteMatching.DenseWordRAM
