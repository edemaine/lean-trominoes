/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMScanBody

/-! # A complete bounded-word sweep over the original endpoint records -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem sweepLoop_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (remaining : Nat)
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (enough : d.1 Reg.index+remaining=input.2.2.length) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.index Reg.edges) scanBody) d result cost ∧
      cost≤(40*(input.1+1)+2)*remaining+2 ∧
      Representation input matching (DenseSearch.scan matching (input.2.2.drop (d.1 Reg.index)) paths) result ∧
      NaturalData.Bounded B result := by
  induction remaining generalizing paths d with
  | zero =>
    have index : d.1 Reg.index=input.2.2.length := by omega
    refine ⟨d,2,Natural.Exec.loop_done ?_,by omega,?_,before⟩
    · simp only [Natural.Holds,index,rep.edges,lt_self_iff_false,not_false_eq_true]
    · simpa only [index,List.drop_length,DenseSearch.scan,List.foldl_nil] using rep
  | succ remaining ih =>
    have within : d.1 Reg.index< input.2.2.length := by omega
    let i : Fin input.2.2.length := ⟨d.1 Reg.index,within⟩
    obtain ⟨middle,firstCost,first,budget,middleRep,middleBound,nextIndex⟩ := scanBody_simulates input matching paths d rep before room inv i rfl
    have middleInv := DenseSearch.discover_invariant (fun l r => (l,r)∈input.2.2) matching paths inv (input.2.2.get i) (List.get_mem ..)
    obtain ⟨result,cost,later,laterBudget,finalRep,finalBound⟩ := ih _ _ middleRep middleInv middleBound
      (by rw [nextIndex]; dsimp [i]; omega)
    have scanEqual : DenseSearch.scan matching (input.2.2.drop (d.1 Reg.index)) paths=
        DenseSearch.scan matching (input.2.2.drop (i.val+1)) (DenseSearch.discover matching paths (input.2.2.get i)) := by
      rw [List.drop_eq_getElem_cons within]
      rfl
    refine ⟨result,firstCost+cost+2,Natural.Exec.loop_more ?_ first later,?_,?_,finalBound⟩
    · simpa only [Natural.Holds,rep.edges] using within
    · rw [Nat.mul_succ]
      omega
    · rw [scanEqual]
      simpa only [nextIndex] using finalRep

theorem sweep_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d)
    (inv : DenseSearch.Invariant (fun l r => (l,r)∈input.2.2) matching paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B) :
    ∃ result cost, Natural.Exec B sweep d result cost ∧ cost≤50*(input.1+1)*(input.2.2.length+1) ∧
      Representation input matching (DenseSearch.scan matching input.2.2 paths) result ∧ NaturalData.Bounded B result := by
  have first : Natural.Exec B (constant Reg.index 0) d (d.set Reg.index 0) 1 :=
    Natural.Exec.atom (Natural.Step.constant d Reg.index 0 (Nat.zero_le B))
  have startRep := rep.set_scalar input matching paths d Reg.index 0 (scalarRegister_of_large _ (by decide)) (by decide)
  obtain ⟨result,cost,later,budget,finalRep,finalBound⟩ := sweepLoop_exec input matching input.2.2.length paths (d.set Reg.index 0)
    startRep inv (first.bounded before) room (by simp [NaturalData.set])
  refine ⟨result,1+cost,first.seq later,?_,?_,finalBound⟩
  · have factor : 40*(input.1+1)+2≤42*(input.1+1) := by omega
    have product := Nat.mul_le_mul_right input.2.2.length factor
    nlinarith
  · simpa only [NaturalData.set,Function.update_self,List.drop_zero] using finalRep

end LeanTrominoes.BipartiteMatching.DenseWordRAM
