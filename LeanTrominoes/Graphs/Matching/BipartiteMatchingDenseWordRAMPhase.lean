/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSearch
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMTerminal
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMAugment

/-! # One complete matching phase refines the correct finite solver -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
open BlockingPath

def PhaseSpec (input : Input) (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1))
    (outcome : Option (State (Fin input.1) (Fin input.2.1))) (d : Data) : Prop :=
  match outcome with
  | none => d.1 Reg.output=0 ∧ Representation input matching paths d
  | some next => d.1 Reg.output=1 ∧ Representation input next paths d

theorem phase_budget (n E searchCost terminalCost tailCost : Nat)
    (a : searchCost≤60*(n+1)^2*(E+1)) (b : terminalCost≤20*(E+1)) (c : tailCost≤20*(n+1)+2) :
    searchCost+terminalCost+tailCost≤120*(n+1)^2*(E+1) := by
  have square : n+1≤(n+1)^2 := by nlinarith
  have p := Nat.mul_le_mul_right (E+1) square
  have q := Nat.mul_le_mul_left ((n+1)^2) (show 1≤E+1 by omega)
  nlinarith

theorem phase_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B) (running : d.1 Reg.output=1) :
    ∃ result cost, Natural.Exec B phase d result cost ∧ cost≤120*(input.1+1)^2*(input.2.2.length+1) ∧
      PhaseSpec input matching (DenseSearch.search matching input.2.2 input.1) (DenseSearch.next matching input.2.2) result ∧
      NaturalData.Bounded B result := by
  let searched := DenseSearch.search matching input.2.2 input.1
  have searchedEq : DenseSearch.search matching input.2.2 input.1=searched := rfl
  have invariant := DenseSearch.search_invariant (fun l r => (l,r)∈input.2.2) matching input.2.2 (fun _ h => h) input.1
  have searchedBound := invariant_paths_bound input matching searched invariant
  obtain ⟨middle,searchCost,searchedRun,searchBudget,middleRep,middleBound⟩ := search_exec input matching paths d rep pathsBound before room
  obtain ⟨ready,terminalCost,terminalRun,terminalBudget,readyRep,readyBound,chosen⟩ := terminal_exec input matching searched middle middleRep middleBound room
  have prefixRun := searchedRun.seq terminalRun
  have readyOutput : ready.1 Reg.output=1 := (prefixRun.register_eq (by decide)).trans running
  cases found : DenseSearch.terminal matching searched input.2.2 with
  | none =>
    have selected : Selected input none ready := by simpa only [found] using chosen
    have condition : Natural.Holds (.eq Reg.foundRight Reg.zero) ready := by simpa only [Natural.Holds,Selected,readyRep.zero] using selected
    let result := ready.set Reg.output 0
    have tail : Natural.Exec B (constant Reg.output 0) ready result 1 := Natural.Exec.atom (Natural.Step.constant ready Reg.output 0 (Nat.zero_le B))
    have branch := Natural.Exec.branch_yes (no := augment) condition tail
    have resultRep := readyRep.set_scalar input matching searched ready Reg.output 0 (scalarRegister_of_large _ (by decide)) (by decide)
    have missing : DenseSearch.next matching input.2.2=none := by simp [DenseSearch.next,Fintype.card_fin,searchedEq,found]
    refine ⟨result,searchCost+(terminalCost+2),searchedRun.seq (terminalRun.seq branch),?_,?_,tail.bounded readyBound⟩
    · have budget := phase_budget input.1 input.2.2.length searchCost terminalCost 2 searchBudget terminalBudget (by omega)
      omega
    · rw [missing]
      exact ⟨by simp [result,NaturalData.set],resultRep⟩
  | some edge =>
    obtain ⟨l,r⟩ := edge
    obtain ⟨member,⟨prior,marked⟩,free⟩ := DenseSearch.terminal_spec matching searched input.2.2 l r found
    have selected : Selected input (some (l,r)) ready := by simpa only [found] using chosen
    have condition : ¬Natural.Holds (.eq Reg.foundRight Reg.zero) ready := by simp only [Natural.Holds,selected.2,readyRep.zero]; omega
    obtain ⟨result,augmentCost,augmentRun,augmentBudget,finalRep,finalBound⟩ := augment_exec input matching searched ready readyRep searchedBound readyBound room l r prior marked selected
    let route := DenseSearch.prepend prior (.last l r)
    have alternating := (invariant.path l prior marked).prepend (.last l r) rfl (Alternating.last member free)
    have simple : route.vertices.Nodup := by
      rw [← routePairs_fst,DenseSearch.prepend_pairs]
      simpa [routePairs] using invariant.simple l prior marked
    have rewriting : DenseSearch.writePairs matching (prior++[(l,r)])=applyRoute matching route := by
      have same := DenseSearch.writePairs_route matching route simple (labels_nodup _ matching route alternating.1 simple)
      simpa only [route,DenseSearch.prepend_pairs,routePairs] using same
    have next : DenseSearch.next matching input.2.2=some (applyRoute matching route) := by
      simp [DenseSearch.next,Fintype.card_fin,searchedEq,found,marked,route]
    have branch := Natural.Exec.branch_no (yes := constant Reg.output 0) condition augmentRun
    refine ⟨result,searchCost+(terminalCost+(augmentCost+2)),searchedRun.seq (terminalRun.seq branch),?_,?_,finalBound⟩
    · have budget := phase_budget input.1 input.2.2.length searchCost terminalCost (augmentCost+2) searchBudget terminalBudget (by omega)
      omega
    · rw [next]
      exact ⟨(augmentRun.register_eq (by decide)).trans readyOutput,by simpa only [rewriting] using finalRep⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
