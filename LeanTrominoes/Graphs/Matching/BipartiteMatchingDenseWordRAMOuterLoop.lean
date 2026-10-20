/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMPhase
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMFailedLoop

/-! # The complete bounded outer loop implements the finite matching solver -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem outerLoop_exec {B : Nat} (input : Input) (remaining : Nat)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (running : d.1 Reg.output=1) (enough : d.1 Reg.outer+remaining=input.1) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.outer Reg.n) outerBody) d result cost ∧
      cost≤(120*(input.1+1)^2*(input.2.2.length+1)+5)*remaining+2 ∧ NaturalData.Bounded B result ∧
      result.1 Reg.output=(if (DenseSearch.run input.2.2 remaining matching).isSome then 1 else 0) := by
  induction remaining generalizing matching paths d with
  | zero =>
    refine ⟨d,2,Natural.Exec.loop_done ?_,by omega,before,?_⟩
    · simp only [Natural.Holds,rep.n]
      omega
    · simpa only [DenseSearch.run,Option.isSome_some,ite_true] using running
  | succ remaining ih =>
    have inside : d.1 Reg.outer< input.1 := by omega
    obtain ⟨middle,phaseCost,phaseRun,phaseBudget,spec,middleBound⟩ := phase_exec input matching paths d rep pathsBound before room running
    have nBound : input.1≤B := by
      have bound : input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
      exact bound.trans room
    have middleOuter : middle.1 Reg.outer=d.1 Reg.outer := phaseRun.register_eq (by decide)
    have middleOne : middle.1 Reg.one=1 := (phaseRun.register_eq (by decide)).trans rep.one
    have middleN : middle.1 Reg.n=input.1 := (phaseRun.register_eq (by decide)).trans rep.n
    let nextData := middle.set Reg.outer (middle.1 Reg.outer+middle.1 Reg.one)
    have incremented : Natural.Exec B (increment Reg.outer) middle nextData 1 := Natural.Exec.atom
      (Natural.Step.add middle Reg.outer Reg.outer Reg.one
        (by rw [middleOuter,middleOne]; exact (show d.1 Reg.outer+1≤ input.1 by omega).trans nBound))
    have branch := Natural.Exec.branch_no (yes := skip)
      (show ¬Natural.Holds (.eq Reg.output Reg.zero) d by simp only [Natural.Holds,running,rep.zero]; decide) phaseRun
    have body : Natural.Exec B outerBody d nextData (phaseCost+3) := by simpa only [outerBody,Nat.add_assoc,Nat.reduceAdd] using branch.seq incremented
    have nextOuter : nextData.1 Reg.outer=d.1 Reg.outer+1 := by simp [nextData,NaturalData.set,middleOuter,middleOne]
    have nextOutput : nextData.1 Reg.output=middle.1 Reg.output := by simp [nextData,NaturalData.set,Reg.output,Reg.outer]
    have nextEnough : nextData.1 Reg.outer+remaining=input.1 := by rw [nextOuter]; omega
    cases next : DenseSearch.next matching input.2.2 with
    | none =>
      simp only [next,PhaseSpec] at spec
      have middleZero : middle.1 Reg.zero=0 := spec.2.zero
      obtain ⟨result,later,finalBound,finalOutput⟩ := failedLoop_exec remaining nextData (body.bounded before) nBound
        (by simp [nextData,NaturalData.set,Reg.n,Reg.outer,middleN])
        (by simp [nextData,NaturalData.set,Reg.one,Reg.outer,middleOne])
        (by simp [nextData,NaturalData.set,Reg.zero,Reg.outer,middleZero]) (by rw [nextOutput]; exact spec.1) nextEnough
      have trace := Natural.Exec.loop_more (c := .lt Reg.outer Reg.n)
        (by simpa only [Natural.Holds,rep.n] using inside) body later
      refine ⟨result,phaseCost+3+(5*remaining+2)+2,trace,?_,finalBound,?_⟩
      · have factor : 5*remaining≤(120*(input.1+1)^2*(input.2.2.length+1)+5)*remaining := Nat.mul_le_mul_right remaining (by omega)
        rw [Nat.mul_succ]
        omega
      · simpa only [DenseSearch.run,next,Option.bind_none,Option.isSome_none,Bool.false_eq_true,ite_false] using finalOutput
    | some nextMatching =>
      simp only [next,PhaseSpec] at spec
      let searched := DenseSearch.search matching input.2.2 input.1
      have nextRep := spec.2.set_scalar input nextMatching searched middle Reg.outer (middle.1 Reg.outer+middle.1 Reg.one)
        (scalarRegister_of_large _ (by decide)) (by decide)
      have nextPathsBound := invariant_paths_bound input matching searched
        (DenseSearch.search_invariant (fun l r => (l,r)∈input.2.2) matching input.2.2 (fun _ h => h) input.1)
      obtain ⟨result,cost,later,budget,finalBound,answer⟩ := ih _ _ _ nextRep nextPathsBound (body.bounded before)
        (by rw [nextOutput]; exact spec.1) nextEnough
      have trace := Natural.Exec.loop_more (c := .lt Reg.outer Reg.n)
        (by simpa only [Natural.Holds,rep.n] using inside) body later
      refine ⟨result,phaseCost+3+cost+2,trace,?_,finalBound,?_⟩
      · rw [Nat.mul_succ]
        omega
      · simpa only [DenseSearch.run,next,Option.bind_some] using answer

end LeanTrominoes.BipartiteMatching.DenseWordRAM
