/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingPhase
import LeanTrominoes.BipartiteMatchingSchedule

/-! # Termination, correctness, and certified successful phases -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]

def OutputSpec (buckets : L → List R) : Option (State L R) → Prop
  | none => ¬ HasFiniteMatching buckets
  | some s => Consistent s ∧ Supported (fun l r => r ∈ buckets l) s ∧ Full s

def roundBudget (buckets : L → List R) : Nat :=
  100*((∑ l, (buckets l).length)+Fintype.card L+Fintype.card R+1)

theorem solve_spec (vertices : List L) (nodup : vertices.Nodup) (complete : ∀ l, l ∈ vertices)
    (buckets : L → List R) (fuel : Nat) (matching : State L R)
    (consistent : Consistent matching) (supported : Supported (fun l r => r ∈ buckets l) matching)
    (lower : Nat) (short : NoShort buckets matching lower)
    (enough : (BreadthSearch.freeVertices vertices matching).length ≤ fuel) :
    OutputSpec buckets (solve vertices buckets fuel matching).matching ∧
    Schedule (Fintype.card L) (BreadthSearch.freeVertices vertices matching).length lower
      (solve vertices buckets fuel matching).trace ∧
    (solve vertices buckets fuel matching).cost ≤
      roundBudget buckets*((solve vertices buckets fuel matching).trace.length+1) := by
  induction fuel generalizing matching lower with
  | zero =>
    have nil : BreadthSearch.freeVertices vertices matching=[] := List.length_eq_zero_iff.mp (by omega)
    have full := roots_empty_full vertices complete matching (by simp [nil])
    simp only [solve,nil,List.isEmpty_nil,if_true,OutputSpec,Schedule,List.length_nil]
    refine ⟨⟨consistent,supported,full⟩,trivial,?_⟩
    rw [BreadthSearch.vertices_length vertices nodup complete]
    simp only [roundBudget,Nat.mul_one,Nat.zero_add]
    omega
  | succ fuel ih =>
    cases empty : (BreadthSearch.freeVertices vertices matching).isEmpty with
    | true =>
      have full := roots_empty_full vertices complete matching empty
      simp only [solve,empty,if_true,OutputSpec,Schedule,List.length_nil]
      refine ⟨⟨consistent,supported,full⟩,trivial,?_⟩
      rw [BreadthSearch.vertices_length vertices nodup complete]
      simp only [roundBudget,Nat.mul_one,Nat.zero_add]
      omega
    | false =>
      have positive : 0 < (BreadthSearch.freeVertices vertices matching).length := by
        cases h : BreadthSearch.freeVertices vertices matching with
        | nil => simp [h] at empty
        | cons l ls => simp
      have bfs := BreadthSearch.search_spec vertices nodup complete buckets matching consistent positive
      have bfsCost := BreadthSearch.search_cost_bound vertices nodup complete buckets matching positive
      simp only [solve,empty,Bool.false_eq_true,if_false]
      cases found : BreadthSearch.search vertices buckets matching with
      | exhausted cost =>
        simp only [found,BreadthSearch.Spec] at bfs
      | deficient distance depth cost =>
        simp only [found,BreadthSearch.Spec] at bfs
        simp only [found,BreadthSearch.Outcome.cost] at bfsCost
        refine ⟨?_,trivial,?_⟩
        · rintro ⟨f,edges⟩
          have hall := hall_of_equiv buckets f edges (BreadthSearch.prefixSet distance depth)
          omega
        · change 16*vertices.length+3+cost+2 ≤ roundBudget buckets*(0+1)
          rw [BreadthSearch.vertices_length vertices nodup complete]
          simp only [roundBudget,Nat.mul_one,Nat.zero_add]
          omega
      | layers distance depth cost =>
        simp only [found,BreadthSearch.Spec] at bfs
        simp only [found,BreadthSearch.Outcome.cost] at bfsCost
        obtain ⟨labels,density,depthPositive,route⟩ := bfs
        have increase := layers_above buckets matching lower short distance depth route
        obtain ⟨nextGood,nextEdges,drop,nextShort⟩ := phase_correct vertices nodup complete buckets matching consistent supported distance depth labels route
        have nextEnough : (BreadthSearch.freeVertices vertices
            (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1).length ≤ fuel := by omega
        obtain ⟨output,trace,bound⟩ := ih _ nextGood nextEdges depth nextShort nextEnough
        have trace' := trace.weaken ((BreadthSearch.freeVertices vertices matching).length-1) (by omega)
        refine ⟨output,⟨positive,le_refl _,increase,density,trace'⟩,?_⟩
        have phaseCost := phase_cost vertices nodup complete buckets matching distance depth
        have current : 16*vertices.length+3+cost+
            (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).2+4 ≤ roundBudget buckets := by
          rw [BreadthSearch.vertices_length vertices nodup complete]
          unfold roundBudget
          omega
        change 16*vertices.length+3+cost+
          (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).2+
          (solve vertices buckets fuel (phase buckets matching distance depth (BreadthSearch.freeVertices vertices matching)).1).cost+4 ≤ _
        simp only [List.length_cons]
        nlinarith

end LeanTrominoes.BipartiteMatching
