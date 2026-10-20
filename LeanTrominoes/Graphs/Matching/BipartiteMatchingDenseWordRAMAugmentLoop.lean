/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMAugmentPair

/-! # Rewriting every stored prefix pair with bounded primitive instructions -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem augmentLoop_exec {B : Nat} (input : Input) (remaining : Nat)
    (matching : State (Fin input.1) (Fin input.2.1))
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (l : Fin input.1) (prior : List (Fin input.1 × Fin input.2.1)) (marked : paths l=some prior)
    (source : d.1 Reg.source=l.val*input.1) (length : d.1 Reg.length=prior.length)
    (enough : d.1 Reg.copyIndex+remaining=prior.length) :
    ∃ result cost, Natural.Exec B (.loop (.lt Reg.copyIndex Reg.length) augmentPair) d result cost ∧ cost≤16*remaining+2 ∧
      Representation input (DenseSearch.writePairs matching (prior.drop (d.1 Reg.copyIndex))) paths result ∧
      NaturalData.Bounded B result := by
  induction remaining generalizing matching d with
  | zero =>
    have index : d.1 Reg.copyIndex=prior.length := by omega
    refine ⟨d,2,Natural.Exec.loop_done ?_,by omega,?_,before⟩
    · simp only [Natural.Holds,index,length,lt_self_iff_false,not_false_eq_true]
    · simpa only [index,List.drop_length,DenseSearch.writePairs] using rep
  | succ remaining ih =>
    have within : d.1 Reg.copyIndex<prior.length := by omega
    let j : Fin prior.length := ⟨d.1 Reg.copyIndex,within⟩
    obtain ⟨middle,first,middleRep,middleBound,nextIndex⟩ := augmentPair_exec input matching paths d rep pathsBound before room l prior marked j source rfl
    have nextSource : middle.1 Reg.source=l.val*input.1 := (first.register_eq (by decide)).trans source
    have nextLength : middle.1 Reg.length=prior.length := (first.register_eq (by decide)).trans length
    obtain ⟨result,cost,later,budget,finalRep,finalBound⟩ := ih _ _ middleRep middleBound nextSource nextLength
      (by rw [nextIndex]; dsimp [j]; omega)
    refine ⟨result,14+cost+2,Natural.Exec.loop_more ?_ first later,by rw [Nat.mul_succ]; omega,?_,finalBound⟩
    · simpa only [Natural.Holds,length] using within
    · rw [List.drop_eq_getElem_cons within,DenseSearch.writePairs]
      simpa only [nextIndex,j,List.get_eq_getElem] using finalRep

end LeanTrominoes.BipartiteMatching.DenseWordRAM
