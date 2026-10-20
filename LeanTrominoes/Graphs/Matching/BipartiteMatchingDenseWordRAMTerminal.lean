/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMTerminalBody

/-! # The complete first-terminal scan on original edge records -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem terminalCandidate_suffix (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1))
    (found : Option (Fin input.1 × Fin input.2.1)) (edge : Fin input.1 × Fin input.2.1)
    (rest : List (Fin input.1 × Fin input.2.1)) :
    found.orElse (fun _ => DenseSearch.terminal matching paths (edge::rest))=
      (terminalCandidate input matching paths found edge).orElse (fun _ => DenseSearch.terminal matching paths rest) := by
  cases found with
  | some previous => rfl
  | none =>
    cases marked : paths edge.1 <;> cases paired : matching.right edge.2 <;>
      simp [terminalCandidate,terminalTest,DenseSearch.terminal,List.find?_cons,marked,paired]

theorem terminalLoop_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (remaining : Nat)
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B) (enough : d.1 Reg.index+remaining=input.2.2.length)
    (found : Option (Fin input.1 × Fin input.2.1)) (selected : Selected input found d) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.index Reg.edges) terminalBody) d result cost ∧ cost≤18*remaining+2 ∧
      Representation input matching paths result ∧ NaturalData.Bounded B result ∧
      Selected input (found.orElse (fun _ => DenseSearch.terminal matching paths (input.2.2.drop (d.1 Reg.index)))) result := by
  induction remaining generalizing found d with
  | zero =>
    have index : d.1 Reg.index=input.2.2.length := by omega
    refine ⟨d,2,Natural.Exec.loop_done ?_,by omega,rep,before,?_⟩
    · simp only [Natural.Holds,index,rep.edges,lt_self_iff_false,not_false_eq_true]
    · cases found <;> simpa [index,DenseSearch.terminal] using selected
  | succ remaining ih =>
    have within : d.1 Reg.index< input.2.2.length := by omega
    let i : Fin input.2.2.length := ⟨d.1 Reg.index,within⟩
    obtain ⟨middle,firstCost,first,budget,middleRep,middleBound,middleSelected,nextIndex⟩ := terminalBody_exec input matching paths d rep before room i rfl found selected
    obtain ⟨result,cost,later,laterBudget,finalRep,finalBound,finalSelected⟩ := ih middle middleRep middleBound
      (by rw [nextIndex]; dsimp [i]; omega) _ middleSelected
    refine ⟨result,firstCost+cost+2,Natural.Exec.loop_more ?_ first later,by rw [Nat.mul_succ]; omega,finalRep,finalBound,?_⟩
    · simpa only [Natural.Holds,rep.edges] using within
    · rw [List.drop_eq_getElem_cons within,terminalCandidate_suffix]
      simpa only [nextIndex,i,List.get_eq_getElem] using finalSelected

theorem terminal_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d)
    (room : (Layout.ofInput input).frontier≤B) :
    ∃ result cost, Natural.Exec B terminal d result cost ∧ cost≤20*(input.2.2.length+1) ∧
      Representation input matching paths result ∧ NaturalData.Bounded B result ∧
      Selected input (DenseSearch.terminal matching paths input.2.2) result := by
  let start := (d.set Reg.foundRight 0).set Reg.index 0
  have first : Natural.Exec B (constant Reg.foundRight 0) d (d.set Reg.foundRight 0) 1 :=
    Natural.Exec.atom (Natural.Step.constant d Reg.foundRight 0 (Nat.zero_le B))
  have second : Natural.Exec B (constant Reg.index 0) (d.set Reg.foundRight 0) start 1 :=
    Natural.Exec.atom (Natural.Step.constant _ Reg.index 0 (Nat.zero_le B))
  have firstRep := rep.set_scalar input matching paths d Reg.foundRight 0 (scalarRegister_of_large _ (by decide)) (by decide)
  have startRep := firstRep.set_scalar input matching paths _ Reg.index 0 (scalarRegister_of_large _ (by decide)) (by decide)
  obtain ⟨result,cost,later,budget,finalRep,finalBound,chosen⟩ := terminalLoop_exec input matching input.2.2.length paths start startRep
    ((first.seq second).bounded before) room (by simp [start,NaturalData.set]) none (by simp [Selected,start,NaturalData.set,Reg.index,Reg.foundRight])
  refine ⟨result,1+(1+cost),first.seq (second.seq later),by omega,finalRep,finalBound,?_⟩
  simpa only [start,NaturalData.set,Function.update_self,List.drop_zero,Option.orElse] using chosen

end LeanTrominoes.BipartiteMatching.DenseWordRAM
