/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSweep
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitializeLoop

/-! # Complete bounded-word alternating-path search -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem searchLoop_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (remaining : Nat)
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (enough : d.1 Reg.round+remaining=input.1) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.round Reg.n) (.seq sweep (increment Reg.round))) d result cost ∧
      cost≤(50*(input.1+1)*(input.2.2.length+1)+3)*remaining+2 ∧
      Representation input matching ((DenseSearch.scan matching input.2.2)^[remaining] paths) result ∧
      NaturalData.Bounded B result := by
  induction remaining generalizing paths d with
  | zero =>
    have round : d.1 Reg.round=input.1 := by omega
    exact ⟨d,2,Natural.Exec.loop_done (by simp only [Natural.Holds,round,rep.n,lt_self_iff_false,not_false_eq_true]),by omega,rep,before⟩
  | succ remaining ih =>
    have inside : d.1 Reg.round< input.1 := by omega
    obtain ⟨middle,firstCost,first,budget,middleRep,middleBound⟩ := sweep_exec input matching paths d rep inv before room
    have round : middle.1 Reg.round=d.1 Reg.round := first.register_eq (by decide)
    have nBound : input.1≤B := by
      have bound : input.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
      exact bound.trans room
    let next := middle.set Reg.round (middle.1 Reg.round+middle.1 Reg.one)
    have incremented : Natural.Exec B (increment Reg.round) middle next 1 :=
      Natural.Exec.atom (Natural.Step.add middle Reg.round Reg.round Reg.one
        (by rw [round,middleRep.one]; exact (show d.1 Reg.round+1≤ input.1 by omega).trans nBound))
    have nextRep := middleRep.set_scalar input matching (DenseSearch.scan matching input.2.2 paths) middle Reg.round (middle.1 Reg.round+middle.1 Reg.one)
      (scalarRegister_of_large _ (by decide)) (by decide)
    have nextInv := DenseSearch.scan_invariant (fun l r => (l,r)∈input.2.2) matching input.2.2 paths inv (fun _ h => h)
    obtain ⟨result,cost,later,laterBudget,finalRep,finalBound⟩ := ih _ _ nextRep nextInv (incremented.bounded middleBound)
      (by simp only [next,NaturalData.set,Function.update_self,round,middleRep.one]; omega)
    refine ⟨result,firstCost+1+cost+2,Natural.Exec.loop_more ?_ (first.seq incremented) later,?_,?_,finalBound⟩
    · simpa only [Natural.Holds,rep.n] using inside
    · rw [Nat.mul_succ]
      omega
    · simpa only [Function.iterate_succ_apply] using finalRep

theorem search_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B) :
    ∃ result cost, Natural.Exec B search d result cost ∧ cost≤60*(input.1+1)^2*(input.2.2.length+1) ∧
      Representation input matching (DenseSearch.search matching input.2.2 input.1) result ∧ NaturalData.Bounded B result := by
  obtain ⟨middle,firstCost,first,firstBudget,middleRep,middleBound⟩ := initializeSearch_exec input matching paths d rep pathBound before room
  have second : Natural.Exec B (constant Reg.round 0) middle (middle.set Reg.round 0) 1 :=
    Natural.Exec.atom (Natural.Step.constant middle Reg.round 0 (Nat.zero_le B))
  have startRep := middleRep.set_scalar input matching (DenseSearch.initial matching) middle Reg.round 0
    (scalarRegister_of_large _ (by decide)) (by decide)
  obtain ⟨result,cost,later,budget,finalRep,finalBound⟩ := searchLoop_exec input matching input.1 (DenseSearch.initial matching)
    (middle.set Reg.round 0) startRep (DenseSearch.initial_invariant _ _) (second.bounded middleBound) room (by simp [NaturalData.set])
  refine ⟨result,firstCost+(1+cost),first.seq (second.seq later),?_,finalRep,finalBound⟩
  have factor : input.1*(input.1+1)≤(input.1+1)^2 := by nlinarith
  have product := Nat.mul_le_mul_right (50*(input.2.2.length+1)) factor
  have slack : 12*input.1+6≤10*(input.1+1)^2*(input.2.2.length+1) := by
    have one : 1≤ input.2.2.length+1 := by omega
    have bound := Nat.mul_le_mul_left (10*(input.1+1)^2) one
    nlinarith
  nlinarith

end LeanTrominoes.BipartiteMatching.DenseWordRAM
